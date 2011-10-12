/* Implementations of some hot perl ops in sljit. */
#include "pp_sljit.h"
#include <perl.h>
#include <sljitLir.h>

#if PERL_VERSION != 14
#  error These operations have not been tested with your version of perl
#endif

// TODO

void emit_pp_nextstate() {
}
