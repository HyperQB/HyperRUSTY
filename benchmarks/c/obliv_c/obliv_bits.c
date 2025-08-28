#include "obliv_bits.h"

// #param(1) @obliv:secrecy
void __obliv_c__assignBitKnown(OblivBit* dest, int value)
{ dest->knownValue = value; dest->unknown=false; }

// #param @obliv:secrecy
void __obliv_c__copyBit(OblivBit* dest,const OblivBit* src)
  { if(dest!=src) *dest=*src; }

// #param(2) @obliv:secrecy
int __obliv_c__bitIsKnown(int* v,const OblivBit* bit)
{ if(known(bit)) *v=bit->knownValue;
  return known(bit);
}

// #param @obliv:secrecy 
void __obliv_c__flipBit(OblivBit* dest) 
{ if(known(dest)) dest->knownValue = !dest->knownValue;
  else currentProto->flipBit(currentProto,dest); 
}

// #param @obliv:secrecy
void __obliv_c__setBitAnd(OblivBit* dest,const OblivBit* a,const OblivBit* b)
{
  if(known(a) || known(b))
  { if(!known(a)) { const OblivBit* t=a; a=b; b=t; }
    if(a->knownValue) __obliv_c__copyBit(dest,b);
    else __obliv_c__assignBitKnown(dest,false);
  }else currentProto->setBitAnd(currentProto,dest,a,b);
}

// #param @obliv:secrecy
void __obliv_c__setBitOr(OblivBit* dest,const OblivBit* a,const OblivBit* b)
{
  if(known(a) || known(b))
  { if(!known(a)) { const OblivBit* t=a; a=b; b=t; }
    if(!a->knownValue) __obliv_c__copyBit(dest,b);
    else __obliv_c__assignBitKnown(dest,true);
  }else currentProto->setBitOr(currentProto,dest,a,b);
}

// #param @obliv:secrecy
void __obliv_c__setBitXor(OblivBit* dest,const OblivBit* a,const OblivBit* b)
{
  int v;
  if(known(a) || known(b))
  { if(!known(a)) { const OblivBit* t=a; a=b; b=t; }
    v = a->knownValue;
    __obliv_c__copyBit(dest,b);
    if(v) __obliv_c__flipBit(dest);
  }else currentProto->setBitXor(currentProto,dest,a,b); 
}

// #param @obliv:secrecy
void __obliv_c__setBitNot(OblivBit* dest,const OblivBit* a)
{ if(known(a)){ *dest=*a; dest->knownValue=!dest->knownValue; }
  else currentProto->setBitNot(currentProto,dest,a); 
}

int main() {
  OblivBit dest = {5, false};
  OblivBit *to_copy = (OblivBit *)malloc(sizeof(OblivBit));
  // __obliv_c__copyBit(&dest, to_copy);
  if (&dest != to_copy) {
    dest = *to_copy;
  }
  return 0;
}
