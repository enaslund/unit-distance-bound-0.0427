def isprime(n):
    if n<2: return False
    if n%2==0: return n==2
    i=3
    while i*i<=n:
        if n%i==0: return False
        i+=2
    return True
def L(a,p):
    a%=p
    if a==0: return 0
    r=pow(a,(p-1)//2,p)
    return 1 if r==1 else -1
