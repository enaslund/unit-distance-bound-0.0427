// Independent blockwise factorization and moment scan for a single H7 octic row.
// The frozen sparse producer is included only for its pinned arithmetic
// prime-label routine and input structs. Its recursive Enumerator is unused.
#define main frozen_sparse_main_unused
#include "../../../../publication/nonabelian-dyadic-lower-bound/research/octic-sparse-moments.cpp"
#undef main

#include <cstdlib>
#include <limits>

static long long local_coefficient(int code, unsigned e) {
    if (std::abs(code) == 2) {
        if (e & 1) return 0;
        unsigned j=e/2;
        long long c=choose(j+3,3);
        if (code < 0 && (j&1)) c=-c;
        return c;
    }
    assert(code==1 || code==-1);
    long long c=choose(e+7,7);
    if (code<0 && (e&1)) c=-c;
    return c;
}

static void fill_twisted_prime_codes(U maxN, U form,
                                     const std::array<mpz_class,12>& eta,
                                     const std::map<U,int>& exceptions,
                                     unsigned twist_mask,
                                     std::vector<std::int8_t>& codes) {
    // Stream prime labels directly into the compact table. This mirrors the
    // pinned arithmetic classifier but avoids materializing its vector<Prime>
    // alongside the N-byte table.
    std::vector<std::int16_t> genus(MODULUS,-1);
    std::array<int,256> actions{};
    for(unsigned v=0;v<256;++v){
        unsigned radical=0,bit=8; bool square=__builtin_parityll(form&v);
        for(unsigned i=0;i<8;++i) for(unsigned j=i+1;j<8;++j,++bit)
            if((form>>bit)&1){
                if((v>>i)&1) radical^=1u<<j;
                if((v>>j)&1) radical^=1u<<i;
                square^=((v>>i)&1)&&((v>>j)&1);
            }
        actions[v]=radical?(square?-2:2):0;
        assert(radical||!square);
    }
    for(U r=1;r<MODULUS;r+=2){
        bool unit=true; for(U p:badprimes) if(r%p==0){unit=false;break;}
        if(!unit) continue;
        unsigned v=(r%4==3); v|=unsigned(r%8==3||r%8==5)<<1;
        for(unsigned i=1;i<7;++i){
            int chi=jacobi(badprimes[i]%r,r); assert(chi);
            if(chi<0) v|=1u<<(i+1);
        }
        genus[r]=v;
    }

    U limit=1; while((limit+1)*(limit+1)<=maxN) ++limit;
    std::vector<bool> small(limit+1,true); std::vector<U> primes;
    for(U p=2;p<=limit;++p) if(small[p]){
        primes.push_back(p);
        if(p<=limit/p) for(U n=p*p;n<=limit;n+=p) small[n]=false;
    }
    const U block=1<<20; std::vector<std::uint8_t> sieve(block);
    for(U lo=2;lo<=maxN;lo+=block){
        U hi=std::min(maxN,lo+block-1); std::fill(sieve.begin(),sieve.begin()+hi-lo+1,1);
        for(U p:primes){
            if(p>hi/p) break;
            U first=std::max(p*p,((lo+p-1)/p)*p);
            for(U n=first;n<=hi;n+=p) sieve[n-lo]=0;
        }
        for(U p=lo;p<=hi;++p) if(sieve[p-lo]){
            if(p<=17) continue;
            int v=genus[p%MODULUS]; assert(v>=0);
            int code=actions[v];
            // Inert primes with p^2>N have zero first local coefficient.
            if(code && p>maxN/p) continue;
            if(!code){
                auto found=exceptions.find(p);
                code=central_sign(p,eta);
                if(found!=exceptions.end()) assert(code==found->second);
                assert(code==1||code==-1);
            }
            if((code==1||code==-1) && __builtin_parity(twist_mask&unsigned(v))) code=-code;
            assert(code==1||code==-1||code==2||code==-2);
            codes[p]=std::int8_t(code);
        }
    }
}

int main(int argc, char** argv) {
    assert(argc==3 && sizeof(long)==8);
    std::ifstream meta(argv[1]), binfile(argv[2]);
    assert(meta && binfile);
    std::string magic;
    meta>>magic; assert(magic=="OCTIC_SPARSE_INPUT_V1");
    word(meta,"sector"); unsigned sector; meta>>sector; assert(sector==1824);
    word(meta,"dimension"); unsigned dimension; meta>>dimension; assert(dimension==8);
    word(meta,"arithmetic"); U form; std::array<mpz_class,12> eta;
    meta>>form; for(auto& x:eta) meta>>x;
    word(meta,"exceptions"); unsigned ne; meta>>ne;
    std::map<U,int> exceptions;
    for(unsigned j=0;j<ne;++j){word(meta,"exception");U p;int s;meta>>p>>s;assert(exceptions.emplace(p,s).second);}
    word(meta,"rows"); unsigned nr; meta>>nr; assert(nr==1);
    Twist row{};
    word(meta,"row"); meta>>row.d>>row.Q>>row.parity>>row.quartic;
    assert(row.d && row.parity==0 && row.quartic==0);
    row.mask=squareclass(row.d);
    assert(row.d==1 && row.mask==0 && row.Q==mpz_class("208190684989647360000"));
    for(unsigned j=0;j<7;++j){
        word(meta,"bad"); U p; meta>>p; assert(p==badprimes[j]);
        for(auto& c:row.bad[j]) meta>>c.r>>c.i;
        assert((row.bad[j][0]==G{1,0}));
        for(auto c:row.bad[j]) assert(c.i==0);
    }
    word(meta,"coefficients"); U prefix_count; meta>>prefix_count; assert(prefix_count==128);
    for(auto& a:row.expected) meta>>a.r>>a.i;
    word(meta,"END"); assert(meta);

    word(binfile,"JOINT_AFE_BINS_V1");
    word(binfile,"degree"); unsigned degree; binfile>>degree; assert(degree==20);
    word(binfile,"multiplier"); unsigned multiplier; binfile>>multiplier; assert(multiplier==1);
    word(binfile,"conductors"); unsigned nq; binfile>>nq; assert(nq==1);
    word(binfile,"conductor"); Layout layout; U count;
    binfile>>layout.Q>>layout.N>>count;
    assert(layout.Q==row.Q && layout.N>=128 && layout.N<=360720360);
    U previous=0;
    for(U k=0;k<count;++k){
        word(binfile,"bin"); Bin b; binfile>>b.index>>b.lo>>b.hi>>b.mid;
        assert(b.lo==previous+1 && b.lo<=b.mid && b.mid<=b.hi && b.hi<=layout.N);
        previous=b.hi; b.moments.resize(degree+1); b.imag.resize(degree+1); b.absolute.resize(degree+1);
        layout.bins.push_back(std::move(b));
    }
    assert(previous==layout.N); word(binfile,"end_conductor"); word(binfile,"END"); assert(binfile);

    // This exact prime classification is deliberately separated from the
    // block coefficient/moment algorithm below. Store only the twisted local
    // code (one byte per n), not any coefficient vector.
    std::vector<std::int8_t> codes(layout.N+1,0);
    fill_twisted_prime_codes(layout.N,form,eta,exceptions,row.mask,codes);

    U root=1; while((root+1)*(root+1)<=layout.N) ++root;
    std::vector<bool> sieve(root+1,true); std::vector<U> small_primes;
    for(U p=2;p<=root;++p) if(sieve[p]){
        small_primes.push_back(p);
        if(p<=root/p) for(U n=p*p;n<=root;n+=p) sieve[n]=false;
    }
    std::array<std::array<long long,40>,7> bad_local{};
    for(unsigned b=0;b<7;++b){
        bad_local[b][0]=1;
        for(unsigned e=1;e<40;++e){
            long long value=0;
            for(unsigned j=1;j<=8 && j<=e;++j)
                value-=row.bad[b][j].r*bad_local[b][e-j];
            bad_local[b][e]=value;
        }
    }

    std::array<G,128> prefix{}; U nonzero=0; std::size_t bin_index=0;
    auto add=[&](U n,long long a){
        assert(a!=0); ++nonzero;
        if(n<=128) prefix[n-1]={a,0};
        while(bin_index+1<layout.bins.size() && layout.bins[bin_index].hi<n) ++bin_index;
        Bin& b=layout.bins[bin_index]; assert(b.lo<=n && n<=b.hi);
        ++b.count; mpz_class mag(static_cast<long>(a<0?-a:a)); b.mass+=mag;
        mpz_class h=mpz_class(n)-b.mid, power=1;
        for(unsigned j=0;j<=degree;++j){
            b.moments[j]+=mpz_class(static_cast<long>(a))*power;
            b.absolute[j]+=mag*power;
            power*=h;
        }
    };

    // Process n=1, then one bounded segment at a time. Every small-prime
    // valuation is removed from rem; the remaining cofactor is either 1 or
    // a single prime > sqrt(N), whose code is in the one-byte table.
    if(layout.bins[0].lo==1 && layout.bins[0].hi>=1) add(1,1);
    const U block_size=1<<20;
    std::vector<std::uint32_t> rem(block_size);
    std::vector<long long> coeff(block_size);
    for(U lo=2;lo<=layout.N;lo+=block_size){
        U hi=std::min(layout.N,lo+block_size-1), len=hi-lo+1;
        for(U j=0;j<len;++j){ rem[j]=std::uint32_t(lo+j); coeff[j]=1; }
        for(U p:small_primes){
            if(p>hi) break;
            U first=((lo+p-1)/p)*p;
            for(U n=first;n<=hi;n+=p){
                U j=n-lo; unsigned e=0;
                while(rem[j]%p==0){rem[j]/=std::uint32_t(p);++e;}
                if(!e || coeff[j]==0) continue;
                long long c;
                if(p<=17){
                    unsigned idx=0; while(badprimes[idx]!=p) ++idx;
                    assert(idx<7 && e<40); c=bad_local[idx][e];
                } else c=local_coefficient(codes[p],e);
                Wide product=Wide(coeff[j])*c;
                assert(-Wide(INT64_MAX)<=product && product<=INT64_MAX);
                coeff[j]=S(product);
            }
        }
        for(U j=0;j<len;++j){
            U n=lo+j; long long a=coeff[j];
            if(a && rem[j]>1){
                U p=rem[j]; int code=codes[p];
                // prime_support omits inert primes with p^2>N because their
                // first local coefficient is zero; here that zero matters.
                if(code==0) a=0;
                else {
                    assert(code==1||code==-1||code==2||code==-2);
                    a=static_cast<long long>(Wide(a)*local_coefficient(code,1));
                }
            }
            if(a) add(n,a);
        }
    }
    std::cout<<"OCTIC_ABSOLUTE_MOMENTS_V1\ndegree "<<degree<<"\nrows 1\n";
    std::cout<<"row "<<row.d<<' '<<row.Q<<' '<<layout.N<<' '<<layout.bins.size()<<' '<<nonzero<<'\n';
    std::cout<<"coefficients 128"; for(G a:prefix) std::cout<<' '<<a.r<<' '<<a.i; std::cout<<'\n';
    for(const auto& b:layout.bins){
        std::cout<<"bin "<<b.index<<' '<<b.lo<<' '<<b.hi<<' '<<b.mid<<' '<<b.mass<<' '<<b.count;
        for(const auto& x:b.moments) std::cout<<' '<<x;
        for(const auto& x:b.imag) std::cout<<' '<<x;
        for(const auto& x:b.absolute) std::cout<<' '<<x;
        std::cout<<'\n';
    }
    std::cout<<"end_row\nEND\n"; assert(std::cout.good());
    std::cerr<<"segmented complete N="<<layout.N<<" nonzero="<<nonzero<<" bins="<<layout.bins.size()<<'\n';
}
