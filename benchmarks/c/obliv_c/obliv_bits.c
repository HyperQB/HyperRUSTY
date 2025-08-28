#include "obliv_bits.h"

int main() {
    int destKnown = 0;
    int destUnknown = false;
    int copyKnown;
    int copyUnknown;
    if ((destKnown != copyKnown) || (destUnknown != copyUnknown)) {
      destKnown = copyKnown;
      destUnknown = copyUnknown;
    }
    return 0;
}
