-- Replay from this directory with:
--     M2 --script verify_global_moh.m2
-- Repaired and successfully executed with Macaulay2 1.26.06 on 2026-09-06.
load "certificate_data.m2";

-- Certificate checks: polynomial matrix equality only.
assert(f * reverseCoefficients == H);
actualPowerProducts = matrix {{
    f_(0,0)^2,
    f_(0,0)*f_(0,1),
    f_(0,0)*f_(0,2),
    f_(0,0)*f_(0,3),
    f_(0,1)^2,
    f_(0,1)*f_(0,2),
    f_(0,1)*f_(0,3),
    f_(0,2)^2,
    f_(0,2)*f_(0,3),
    f_(0,3)^2
    }};
assert(entries actualPowerProducts == entries powerProducts);
assert(entries(powerProducts * substitute(powerScales,S)) == entries(H * powerCoefficients));
print "PASS: two reverse membership identities and all ten square identities";

-- Independently recompute the specified polynomial parametrization kernel.
A = QQ[t];
rho = map(A,S,{t^6+t^31,t^8,t^10});
P = ideal f;
Q = ideal H;
assert(ker rho == P);
assert(rho(H_(0,0)) == 0_A);
assert(rho(H_(0,1)) == 0_A);
print "PASS: exact global parametrization kernel";

-- Redundant ideal computations, independent of the supplied coefficients.
assert(isSubset(P^2,Q));
assert(isSubset(Q,P));
assert(codim P == 2);
assert(codim Q == 2);
print "PASS: P^2 is contained in Q, and Q is contained in P";

-- Also replay the short constructive origin of the two witnesses.
assert(det rowChange == 216);
MP = rowChange * Phi;
M = submatrix(MP,{0,1,2},{0,1,2});
assert(entries M == entries transpose M);
assert(det M == -16*H_(0,0));
adjM = matrix {{
    M_(1,1)*M_(2,2)-M_(1,2)*M_(2,1),
    M_(0,2)*M_(2,1)-M_(0,1)*M_(2,2),
    M_(0,1)*M_(1,2)-M_(0,2)*M_(1,1)
    },{
    M_(1,2)*M_(2,0)-M_(1,0)*M_(2,2),
    M_(0,0)*M_(2,2)-M_(0,2)*M_(2,0),
    M_(0,2)*M_(1,0)-M_(0,0)*M_(1,2)
    },{
    M_(1,0)*M_(2,1)-M_(1,1)*M_(2,0),
    M_(0,1)*M_(2,0)-M_(0,0)*M_(2,1),
    M_(0,0)*M_(1,1)-M_(0,1)*M_(1,0)
    }};
r = submatrix(MP,{3},{0,1,2});
assert((r * adjM * transpose r)_(0,0) == 36*H_(0,1));
print "PASS: globally invertible row change and both symmetric determinant formulas";
print "GLOBAL MOH CERTIFICATE VERIFIED OVER QQ";
exit 0;
