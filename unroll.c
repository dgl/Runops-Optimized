#include "unroll.h"
#include <sljitLir.h>

#ifdef DEBUG
void debugf(void *f, ...) {
  va_list ap;
  va_start(ap, f);
  if (getenv("RUNOPS_OPTIMIZED_DEBUG"))
      vfprintf(stderr, f, ap);
  va_end(f);
}
#define DEBUGf(x) debugf x;
#else
#define DEBUGf(x)
#endif

/*** Local data structures ***/

struct oplabel {
    struct sljit_label *label;
    OP *op;
    struct oplabel *next;
};

struct needjump {
    struct sljit_jump *jump;
    OP *op_to;
    struct needjump *next;
};

struct needjump* needjumps = NULL;
struct oplabel* labels = NULL;

/*** Static prototypes ***/
static void unroll_tree(pTHX_ struct sljit_compiler* compiler, HV* seenops,
    OP* op, OP* end);
static void unroll_branching_op(struct sljit_compiler* compiler, HV* seenops,
    OP* op, OP* next, OP* other);
static void unroll_op(pTHX_ struct sljit_compiler* compiler, OP* op);

static void emit_jump(struct sljit_compiler* compiler, OP* op);
static void emit_label(struct sljit_compiler* compiler, OP* op);
static void fixup_jumps(struct sljit_compiler* compiler, struct needjump* jump,
    struct oplabel* label);

static const char* format_hex(void* inaddr);

/******/

void unroll_this(pTHX_ OP* op) {
    struct sljit_compiler* compiler = sljit_create_compiler();
    HV* seenops = newHV();

#ifdef DEBUG
    if (getenv("RUNOPS_OPTIMIZED_DEBUG")) {
        CV *runcv = Perl_find_runcv(NULL);
        sljit_compiler_verbose(compiler, stderr);

        DEBUGf(("Unroll %s::%s cv=%p, op=%p (%s)\n", HvNAME_get(CvSTASH(runcv)),
              GvENAME(CvGV(runcv)), runcv, op, sljit_get_platform_name()));
    }
#endif

    sljit_emit_enter(compiler, 0, 2, 1, 0);
    unroll_tree(compiler, seenops, op, NULL);
    fixup_jumps(compiler, needjumps, labels);
    // This is needed for things that drop off the runloop without a
    // return, e.g. S_sortcv. TODO: Make conditional?
    sljit_emit_return(compiler, SLJIT_MEM, (sljit_w) &PL_op);

    op->op_ppaddr = sljit_generate_code(compiler);
    op->op_spare = 3;
    DEBUGf(("Code at %p\n", op->op_ppaddr));

    labels = NULL;
    needjumps = NULL;
    SvREFCNT_dec(seenops);
    sljit_free_compiler(compiler);
}

static void unroll_tree(pTHX_ struct sljit_compiler* compiler, HV* seenops,
    OP* op, OP* end)
{
    // XXX: This basically is the algorithm from walk_exec in B::Concise, but I
    // think it could be done better. (Maybe core will get something like
    // codegen?).

    while (op && op != end) {

        const char* op_hex = format_hex(op);

        // Have we visited this op already?
        if (hv_exists(seenops, op_hex, strlen(op_hex))) {
            DEBUGf(("  ;; Already seen %s [0x%s]\n", OP_NAME(op), op_hex));
            // Insert jump to it
            emit_jump(compiler, op);
            // We know we have followed all the next pointers for this chain,
            // so:
            break;
        }

        // Seen op
        hv_store(seenops, op_hex, 0, &PL_sv_yes, strlen(op_hex));

        if (op->op_type == OP_CUSTOM) {
            // All bets are off
            sljit_emit_return(compiler, SLJIT_MEM, (sljit_w) &PL_op);
        }

        else if (OP_CLASS(op) == OA_LOGOP) {
            unroll_branching_op(compiler, seenops, op, op->op_next,
                    cLOGOPx(op)->op_other);
        }

        else if (op->op_type == OP_SUBST
                && cPMOPx(op)->op_pmstashstartu.op_pmreplstart) {
            unroll_branching_op(compiler, seenops, op, op->op_next,
                    cPMOPx(op)->op_pmstashstartu.op_pmreplstart);
        }

        else if (op->op_type == OP_GREPSTART || op->op_type == OP_MAPSTART) {
            unroll_branching_op(compiler, seenops, op, op->op_next->op_next,
                    cLOGOPx(op->op_next)->op_other);
        }

        else if (op->op_type == OP_NEXT || op->op_type == OP_LAST
              || op->op_type == OP_REDO) {
            sljit_emit_return(compiler, SLJIT_MEM, (sljit_w) &PL_op);
            //need_patch = 1; XXX
        }

        else if (op->op_type == OP_FLIP || op->op_type == OP_GOTO) {
            sljit_emit_return(compiler, SLJIT_MEM, (sljit_w) &PL_op);
            //need_patch = 1; XXX
        }

        else if (op->op_type == OP_ENTERSUB) {
            sljit_emit_return(compiler, SLJIT_MEM, (sljit_w) &PL_op);
            //need_patch = 1; XXX
        }

        else if (op->op_type == OP_RETURN || op->op_type == OP_LEAVESUB
              || op->op_type == OP_REQUIRE) {
            // XXX: leavesublv?
            unroll_op(compiler, op);
            sljit_emit_return(compiler, SLJIT_MEM, (sljit_w) &PL_op);
        }

        else {
            unroll_op(compiler, op);
#ifdef DEBUG
            // Ensure returned OP is actually the one we expect
            struct sljit_jump *jump1 = sljit_emit_cmp(compiler, SLJIT_C_EQUAL,
                SLJIT_RETURN_REG, 0, SLJIT_IMM, (sljit_w) op->op_next);
            sljit_emit_op0(compiler, SLJIT_BREAKPOINT);
            sljit_set_label(jump1, sljit_emit_label(compiler));
#endif
        }
        op = op->op_next;
    }
}

static void emit_jump(struct sljit_compiler* compiler, OP* op)
{
    struct sljit_jump* jump = sljit_emit_jump(compiler, SLJIT_JUMP);
    struct needjump* fixup = sljit_alloc_memory(compiler, sizeof *fixup);

    fixup->jump = jump;
    fixup->op_to = op;

    fixup->next = needjumps;
    needjumps = fixup;
}

static void emit_label(struct sljit_compiler* compiler, OP* op)
{
    struct sljit_label* label = sljit_emit_label(compiler);
    struct oplabel *oplabel = sljit_alloc_memory(compiler, sizeof *oplabel);

    oplabel->label = label;
    oplabel->op = op;

    oplabel->next = labels;
    labels = oplabel;
}

static void unroll_branching_op(struct sljit_compiler* compiler, HV* seenops,
    OP* op, OP* next, OP* other)
{
    OP *i = other;
    OP *converge = NULL;

    unroll_op(compiler, op);

    // TODO: Generalise emit_jump a bit to save this extra jump
    struct sljit_jump *jump_other = sljit_emit_cmp(compiler,
            SLJIT_C_EQUAL, SLJIT_RETURN_REG, 0, SLJIT_IMM, (sljit_w) other);
    emit_jump(compiler, next);
    sljit_set_label(jump_other, sljit_emit_label(compiler));

    do {
        OP *j = op;

        do {
            if (j == i) {
                converge = i;
                goto done;
            }
        } while ((j = j->op_next));
    } while ((i = i->op_next));

done:
    if (!converge)
        Perl_croak("Runops::Optimized panic: No idea where these ops converge");

    DEBUGf(("  ;; %p converges at %p\n", other, converge));

    unroll_tree(aTHX_ compiler, seenops, other, converge);

    if (next != converge) {
        DEBUGf(("  ;; %p jump needed\n", converge));
        emit_jump(compiler, converge);
    }
}

static void unroll_op(pTHX_ struct sljit_compiler* compiler, OP* op)
{
    DEBUGf(("  ; %s [%p]\n", OP_NAME(op), op));

    emit_label(compiler, op); // TODO(dgl): Can we avoid doing this for every op?
    sljit_emit_ijump(compiler, SLJIT_CALL0, SLJIT_IMM, (sljit_w) op->op_ppaddr);
    sljit_emit_op1(compiler, SLJIT_MOV, SLJIT_MEM, (sljit_w) &PL_op, SLJIT_RETURN_REG, 0);
}

static void fixup_jumps(struct sljit_compiler* compiler, struct needjump* jump,
    struct oplabel *label)
{
    while (jump) {
        struct oplabel *l = label;

        while (l) {
            if (l->op == jump->op_to) {
                sljit_set_label(jump->jump, l->label);
                goto done;
            }
            l = l->next;
        }
        Perl_croak("Unable to resolve jump for %p [%s]", jump->op_to, OP_NAME(jump->op_to));
done:   jump = jump->next;
    }
}

// XXX: Hacky, but rather than fixing this consider the whole reuse of HV for
// remembering seen ops thing.
static const char* format_hex(void* inaddr)
{
    static char ret[16 + 1]; // 64-bits as hex + NUL
    long addr = (long)inaddr;
    char *retval = ret + sizeof ret;
    *--retval = '\0';
    do {
        *--retval = PL_hexdigit[addr & 15];
    } while (addr >>= 4);
    return retval;
}

