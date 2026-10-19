-- Exact computation for p = x^2 + b*x + a, with a,b in QQ.
-- Run: M2 --script macaulay2/noposroots.m2
-- Or load this file in M2 and call quadraticMultiple(a,b,maxIndex).
-- Comments and sequence indices agree with noposroots.tex.

quadraticMultiple = (a,b,maxIndex) -> (
    if not (instance(a,ZZ) or instance(a,QQ)) or
       not (instance(b,ZZ) or instance(b,QQ)) then
        error "expected integer or rational coefficients (use e.g. -19/10)";
    if not instance(maxIndex,ZZ) or maxIndex < 2 then
        error "expected an integer maxIndex >= 2";
    a = a * 1_QQ;
    b = b * 1_QQ;
    R := QQ[symbol x];
    t := R_0;
    p := t^2 + b*t + a;
    delta := b^2 - 4*a;

    -- These cases have a positive real root, so no such q exists.
    if a < 0 or (b < 0 and delta >= 0) then return new HashTable from {
        "status" => "positive real root: no nonnegative multiple exists",
        "p" => p, "discriminant" => delta,
        "y" => null, "n" => null, "q" => null, "product" => null
        };

    -- When a=0 the recurrence is undefined; here b>=0 and q=1 works.
    if a == 0 then return new HashTable from {
        "status" => "already has nonnegative coefficients (a=0)",
        "p" => p, "discriminant" => delta,
        "y" => null, "n" => 1, "q" => 1_R, "product" => p
        };

    -- y_0=0, y_1=1; compute through the first nonpositive term y_k.
    values := new MutableList from (maxIndex+1 : 0_QQ);
    values#1 = 1_QQ;
    k := 1;
    while k < maxIndex and values#k > 0 do (
        k = k+1;
        values#k = -(b/a)*values#(k-1) - (1/a)*values#(k-2);
        );
    sequence := apply(k+1, j -> values#j);
    if values#k > 0 then return new HashTable from {
        "status" => "index limit reached: increase maxIndex",
        "p" => p, "discriminant" => delta,
        "y" => sequence, "n" => null, "q" => null, "product" => null
        };

    n := k-1;
    q := sum(n, j -> values#(j+1)*t^j);
    product := p*q;
    boundary := a - a*values#(n+1)*t^n + values#n*t^(n+1);
    assert(product == boundary);
    assert(q != 0);
    assert(a > 0 and values#n > 0 and values#(n+1) <= 0);
    new HashTable from {
        "status" => "success",
        "p" => p, "discriminant" => delta,
        "y" => sequence, "n" => n, "q" => q, "product" => product
        }
    );

-- Example from the note. Change these three inputs to explore other quadratics.
a = 5;
b = -19/10;
maxIndex = 10000;
result = quadraticMultiple(a,b,maxIndex);
print result;
