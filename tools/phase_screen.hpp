// Shared bounded phase screening, not a proof of equivalence.
// Reject the FIRST return boundary even when its tape or number is wrong.
#pragma once
#include <array>
#include <cstdint>
#include <vector>
#ifndef MACHINE_STATES
#define MACHINE_STATES 25
#endif
#ifndef PHASE_FACTOR
#define PHASE_FACTOR 3
#endif
#ifndef CLASSIFICATION_OFFSET
#define CLASSIFICATION_OFFSET -1
#endif
#ifndef SUCCESS_CERTIFICATES
#define SUCCESS_CERTIFICATES 0
#endif
static_assert(MACHINE_STATES<=32, "Trace masks use two bits per state");
struct Edge { int w,d,q; bool operator==(const Edge&o)const{return w==o.w&&d==o.d&&q==o.q;} };
using Machine=std::array<std::array<Edge,2>,MACHINE_STATES>;
struct Fixture {int kind,n,p;bool success;int baseline_steps;};
static long long steps_run=0;
static uint64_t visited;
int run(const Machine&m,int dead,int keep,const Fixture&f,int factor=PHASE_FACTOR,int start=0) {
 visited=0;std::array<unsigned char,1024> tape{}; int h=512;int q=f.kind==0?start:f.kind==1?21:(f.kind==2||f.kind==4)?0:17;int count=0;
 auto map=[&](int x){return x==dead?keep:x;};q=map(q);
 if(f.kind==1||f.kind==2||f.kind==4){for(int i=0;i<f.n;i++)tape[512+i]=1;count=f.n;if(f.kind==1)h+=f.n;}
 if(f.kind==3){for(int i=-f.p;i<=f.n;i++)tape[512+i]=1;count=f.p+f.n+1;}
 int maxcount=count+12;
 int limit=f.baseline_steps*factor+100;
#if SUCCESS_CERTIFICATES
 int call_head=0, call_input=0;bool pending=false;std::vector<int> tested_primes;
 auto prime=[](int n){if(n<2)return false;for(int d=2;d*d<=n;d++)if(n%d==0)return false;return true;};
#endif
 for(int s=0;s<limit;s++) {
#if SUCCESS_CERTIFICATES
  if(f.kind==1&&q==map(0)&&tape[h]&&!pending){
   call_head=h;call_input=0;while(h+call_input<1024&&tape[h+call_input])call_input++;pending=true;
  }
#endif
  steps_run++;visited |= 1ULL<<(2*q+tape[h]);Edge e=m[q][tape[h]];
  if(e.q<0) return (f.kind==1&&!f.success)?1:0;
  count+=e.w-tape[h];tape[h]=e.w;h+=e.d;q=e.q;
  if(h<128||h>=896||q==dead||count>maxcount) return 0;
#if SUCCESS_CERTIFICATES
  if(pending&&h==call_head+CLASSIFICATION_OFFSET&&(q==map(16)||q==map(20))){
   if((q==map(20))!=prime(call_input))return 0;
   if(q==map(20))tested_primes.push_back(call_input);
   pending=false;
  }
#endif
  auto block=[&](int lo,int hi){if(lo<0||hi>1024||hi-lo!=count)return false;for(int i=lo;i<hi;i++)if(!tape[i])return false;return true;};
  if(f.kind==2||f.kind==4) {
   if((f.kind==4?h<=512+CLASSIFICATION_OFFSET:h==511)&&(q==map(16)||q==map(20)))
    return map(16)!=map(20)&&q==map(f.success?20:16)&&(f.kind==4||block(512,512+f.n));
  } else if(f.kind==3) {
   if(q==map(17)&&tape[h]){
    int lo=h;while(tape[lo-1])lo--;
    if(block(lo,lo+count))return !f.success&&count==f.p+f.n+1&&h-lo==f.p-1;
   }
   if(q==map(21)&&!tape[h]&&count>0&&block(h-count,h))
    return f.success&&count==f.p+f.n+2;
  } else {
   int wanted=f.kind==0?4:f.n+2;
   if(q==map(21)&&!tape[h]&&count>0&&block(h-count,h)) {
#if SUCCESS_CERTIFICATES
    if(f.kind==1&&f.success){
     bool certified=false;for(int a:tested_primes)for(int b:tested_primes)if(a+b==f.n)certified=true;
     if(!certified)return 0;
    }
#endif
    return f.success&&count==wanted;
   }
  }
 }
 return 0;
}
