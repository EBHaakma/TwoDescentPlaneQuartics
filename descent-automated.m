Attach("routines.m");
_<x>:=PolynomialRing(Rationals());
import "routines.m": syzquads;

load "div_arithmetic.m";

load "two_descent.m";

load "isotropic_flag_ordering.m";

//input the vector u representing C, the list of prime divisors of d, 
//and the Steiner system representing the isogeny phi.
//if -1 divides d, then run 'real_case.sage' first.
//this code will output a text file 'auto_output' that contains
//information on each prime and the final rank of the 2-Selmer group and phi-Selmer group.

u := [ -3, -1, 5, 5, -4, 6 ];
d_div := [ 37, 877 ];
Steiner := [ 20, 10, 23, 9, 2, 28, 17, 7, 11, 19, 6, 18 ];

d := &*d_div;
d_prime_div := Exclude(d_div, -1);

time btr:=BitangRecord(u);
C:=Curve(Proj(Parent(btr`f)),btr`f);
rational_points:=&join[Support(Scheme(C,l)): l in btr`bitangs];
bad_primes := [F[1] : F in Factorization(Numerator(DixmierOhnoInvariants(C)[13]))];
prime_lst := Sort(Setseq(Seqset(d_prime_div cat bad_primes cat [2])));
HS,QtoHS:=pSelmerGroup(2,{s : s in prime_lst});
HS6,embHS,projHS:=DirectSum([HS: i in [1..6]]);
selmer_candidate:=HS6;
bitang_eval := Matrix(28,28,[MonomialCoefficient(Resultant(cp[1]*LeadingCoefficient(cp[1]),
Evaluate(l,cp[2])*LeadingCoefficient(Evaluate(l,cp[2])),1),
Parent(cp[1]).2^2): cp in btr`ContactPoints, l in btr`bitangs]);

prime_lst;

VecF2 := VectorSpace(GF(2), 6);
ZZ := Integers();
BitangentLabeling := [
VecF2![ 0, 0, 1, 1, 0, 0 ],
VecF2![ 1, 0, 1, 1, 0, 0 ],
VecF2![ 1, 0, 0, 0, 1, 1 ],
VecF2![ 1, 1, 0, 0, 0, 1 ],
VecF2![ 1, 0, 1, 0, 0, 1 ],
VecF2![ 1, 0, 0, 1, 0, 1 ],
VecF2![ 0, 0, 1, 1, 0, 1 ],
VecF2![ 0, 1, 0, 0, 1, 1 ],
VecF2![ 0, 1, 1, 1, 0, 0 ],
VecF2![ 0, 0, 1, 1, 1, 0 ],
VecF2![ 0, 1, 0, 1, 1, 0 ],
VecF2![ 0, 1, 1, 0, 1, 0 ],
VecF2![ 1, 1, 0, 0, 1, 0 ],
VecF2![ 1, 1, 1, 1, 0, 0 ],
VecF2![ 1, 0, 1, 1, 1, 0 ],
VecF2![ 1, 1, 0, 1, 1, 0 ],
VecF2![ 1, 1, 1, 0, 1, 0 ],
VecF2![ 0, 1, 0, 0, 1, 0 ],
VecF2![ 1, 0, 0, 0, 0, 1 ],
VecF2![ 1, 1, 1, 0, 0, 1 ],
VecF2![ 1, 1, 0, 1, 0, 1 ],
VecF2![ 0, 1, 1, 1, 0, 1 ],
VecF2![ 1, 0, 1, 0, 1, 1 ],
VecF2![ 1, 0, 0, 1, 1, 1 ],
VecF2![ 0, 0, 1, 1, 1, 1 ],
VecF2![ 1, 1, 1, 1, 1, 1 ],
VecF2![ 0, 1, 0, 1, 1, 1 ],
VecF2![ 0, 1, 1, 0, 1, 1 ]
];
VB := VectorSpaceWithBasis([BitangentLabeling[i] : i in [2..7]]);

proj_vec1 := VecF2!Coordinates(VB, BitangentLabeling[Steiner[1]]) + VecF2!Coordinates(VB, BitangentLabeling[Steiner[2]]);
proj_vec2 := VecF2!Coordinates(VB, BitangentLabeling[Steiner[1]]) + VecF2!Coordinates(VB, BitangentLabeling[Steiner[3]]);
proj_vec3 := VecF2!Coordinates(VB, BitangentLabeling[Steiner[5]]) + VecF2!Coordinates(VB, BitangentLabeling[Steiner[7]]);

HS3,embHS3,projHS3:=DirectSum([HS: i in [1..3]]);
proj_selmer_candidate := HS3;

for p in prime_lst do
    
    PrintFile("auto_output.txt", "p = " cat Sprint(p));
    print("p = " cat Sprint(p));

    time Desc := InitDescentFunc(btr, p, d);
    
    PrintFile("auto_output.txt", "extension: " cat Desc`extension);
    
    HStoHp:=hom<HS->Desc`Hp| [Desc`QptoHp(g@@QtoHS): g in OrderedGenerators(HS)]>;
    procedural_map:=func< a | &*[Desc`embHp[i](HStoHp(projHS[i](a))) : i in [1..6]]>;
    HS6toHp6:=hom<HS6->Desc`Hp6 | [procedural_map(a): a in OrderedGenerators(HS6)]>;
    
    Zp := pAdicRing(p, 50);
    Qp := pAdicField(p, 50);
    PZp<x> := PolynomialRing(Zp);
    if p ne 2 then
        assert exists(nqr){a: a in [1..p-1] | LegendreSymbol(a,p) eq -1};
        a := nqr;
        Unram<alpha> := ext<Zp | x^2 - a>;
        PUnram<xU> := PolynomialRing(Unram);
        Ram<beta> := ext<Unram | xU^2 - p>;
    end if;
    
    found_image := sub<Desc`Hp6 | 0>;
    
    if Desc`extension eq "no extension" then
        
        //first check images of degree 2 contact points
        for cp in [1..28] do
            images := [];
            for i in [1..7] do
                v := Qp!bitang_eval[i][cp];
                if (v + BigO(Qp!p^50)) eq BigO(Qp!p^Minimum(AbsolutePrecision(v), 50)) then
                    for triple in btr`UsefulTriples[i] do
                        v := &*[Qp!bitang_eval[k][cp] : k in triple[1]];
                        if (v + BigO(Qp!p^50)) ne BigO(Qp!p^Minimum(AbsolutePrecision(v), 50)) then
                            break triple;
                        end if;
                    end for;
                end if;
                if (v + BigO(Qp!p^50)) eq BigO(Qp!p^Minimum(AbsolutePrecision(v), 50)) then
                    print "skip";
                    continue cp;
                end if;
                Append(~images, v);
            end for;
            w := [Desc`QptoHp(n) : n in images];
            w_div := [w[j] - w[1] : j in [2..7]];
            image := &+[Desc`embHp[i](w_div[i]) : i in [1..6]];
            if not(image in found_image) then
                found_image := sub<Desc`Hp6 | OrderedGenerators(found_image) cat [image]>;
            end if;
            ab := #AbelianInvariants(found_image);
            PrintFile("auto_output.txt", Sprint(ab));
        end for;
        
        //then check images of degree 1 contact points
        for vP1 in Desc`ContactPoints do
            index := 0;
            images := [];
            for i in [1..7] do
                v := &*[Evaluate(btr`bitangs[i], vP) : vP in [vP1, Desc`PQp]];
                if (v + BigO(Qp!p^50)) eq BigO(Qp!p^Minimum(AbsolutePrecision(v), 50)) then
                    for triple in btr`UsefulTriples[i] do
                        sub_poly := triple[2]*&*[btr`bitangs[k] : k in triple[1]];
                        v := &*[Evaluate(sub_poly, vP) : vP in [vP1, Desc`PQp]];
                        if (v + BigO(Qp!p^50)) ne BigO(Qp!p^Minimum(AbsolutePrecision(v), 50)) then
                            break triple;
                        end if;
                    end for;
                end if;
                if (v + BigO(Qp!p^50)) eq BigO(Qp!p^Minimum(AbsolutePrecision(v), 50)) then
                    print "skip";
                    continue vP1;
                end if;
                Append(~images, v);
            end for;
            w := [Desc`QptoHp(n) : n in images];
            w_div := [w[j] - w[1] : j in [2..7]];
            image := &+[Desc`embHp[i](w_div[i]) : i in [1..6]];
            if not(image in found_image) then
                found_image := sub<Desc`Hp6 | OrderedGenerators(found_image) cat [image]>;
            end if;
            ab := #AbelianInvariants(found_image);
            PrintFile("auto_output.txt", Sprint(ab));
        end for;
    
    elif Desc`extension eq "unramified" then
        count := AssociativeArray(Desc`Hp6);
        
        //first search multiples of random points
        for i in [1..100] do
            vP1 := Desc`randpt();
            vP2 := Desc`randpt();
            vP3 := Desc`randpt();
            PrintFile("auto_output.txt", Sprint([vP1, vP2, vP3]));

            D1 := Desc`DivFromPoints(vP1, vP2, vP3);
            mlst := AssociativeArray();
            mlst[1] := D1;
            D := D1;

            for k in Desc`ord_divs do
                _, mlst := Desc`find_mult(mlst, k);

                if k mod 2 eq 0 then
                    if Desc`IsSigmaAntiInv(mlst[k]) then
                        PrintFile("auto_output.txt", "Success at k= " cat Sprint(k));

                        Ddiv, mlst := Desc`find_mult(mlst, k div 2);
                        
                        try
                            sigma_vec, tau_vec := Desc`FindTwoTors(Ddiv);
                        catch e
                            print e;
                            continue i;
                        end try;

                        try
                            Qp_conv := Desc`LocalImageFromVecs(sigma_vec, tau_vec);
                        catch e
                            print e;
                            continue i;
                        end try;
                
                        found_image := sub<Desc`Hp6 | OrderedGenerators(found_image) cat [Qp_conv]>;
                        PrintFile("auto_output.txt", Sprint(#AbelianInvariants(found_image)) cat " " cat Sprint(Qp_conv));
                        if IsDefined(count, Qp_conv) then
                            count[Qp_conv] := count[Qp_conv] + 1;
                        else
                            count[Qp_conv] := 1;
                        end if;

                        if #AbelianInvariants(found_image) eq 5 then
                            break i;
                        else
                            continue i;
                        end if;
                    end if;
                end if;
            end for;
    
            error "miss";
        end for;
        
        //then search multiples of points lying near the singularity
        for i in [1..100] do
            vP1 := Desc`randptQ(Desc`singularity);
            vP2 := Desc`randpt();
            vP3 := Desc`randpt();
            PrintFile("auto_output.txt", Sprint([vP1, vP2, vP3]));

            D1 := Desc`DivFromPoints(vP1, vP2, vP3);
            mlst := AssociativeArray();
            mlst[1] := D1;
            D := D1;

            for k in Desc`ord_divs do
                _, mlst := Desc`find_mult(mlst, k);

                if k mod 2 eq 0 then
                    if Desc`IsSigmaAntiInv(mlst[k]) then
                        PrintFile("auto_output.txt", "Success at k= " cat Sprint(k));

                        Ddiv, mlst := Desc`find_mult(mlst, k div 2);
                        
                        try
                            sigma_vec, tau_vec := Desc`FindTwoTors(Ddiv);
                        catch e
                            print e;
                            continue i;
                        end try;

                        try
                            Qp_conv := Desc`LocalImageFromVecs(sigma_vec, tau_vec);
                        catch e
                            print e;
                            continue i;
                        end try;
                
                        found_image := sub<Desc`Hp6 | OrderedGenerators(found_image) cat [Qp_conv]>;
                        PrintFile("auto_output.txt", Sprint(#AbelianInvariants(found_image)) cat " " cat Sprint(Qp_conv));
                        if IsDefined(count, Qp_conv) then
                            count[Qp_conv] := count[Qp_conv] + 1;
                        else
                            count[Qp_conv] := 1;
                        end if;

                        if #AbelianInvariants(found_image) eq 6 then
                            break i;
                        else
                            continue i;
                        end if;
                    end if;
                end if;
            end for;
    
            error "miss";
        end for;
        
        for K in Keys(count) do
            PrintFile("auto_output.txt", "Number found of " cat Sprint(K) cat ": " cat Sprint(count[K]));
        end for;
        
    elif Desc`extension eq "ramified, invariant" then
        count := AssociativeArray(Desc`Hp6);
        
        //first search multiples of random points
        for i in [1..100] do
            vP1 := Desc`randpt();
            vP2 := Desc`randpt();
            vP3 := Desc`randpt();
            PrintFile("auto_output.txt", Sprint([vP1, vP2, vP3]));

            D1 := Desc`DivFromPoints(vP1, vP2, vP3);
            mlst := AssociativeArray();
            mlst[1] := D1;
            D := D1;

            for k in Desc`ord_divs do
                _, mlst := Desc`find_mult(mlst, k);

                if k mod 2 eq 0 then
                    if Desc`IsTauAntiInv(mlst[k]) then
                        PrintFile("auto_output.txt", "Success at k= " cat Sprint(k));

                        Ddiv, mlst := Desc`find_mult(mlst, k div 2);
                        
                        try
                            sigma_vec, tau_vec := Desc`FindTwoTors(Ddiv);
                        catch e
                            print e;
                            continue i;
                        end try;

                        try
                            Qp_conv := Desc`LocalImageFromVecs(sigma_vec, tau_vec);
                        catch e
                            print e;
                            continue i;
                        end try;
                
                        found_image := sub<Desc`Hp6 | OrderedGenerators(found_image) cat [Qp_conv]>;
                        PrintFile("auto_output.txt", Sprint(#AbelianInvariants(found_image)) cat " " cat Sprint(Qp_conv));
                        if IsDefined(count, Qp_conv) then
                            count[Qp_conv] := count[Qp_conv] + 1;
                        else
                            count[Qp_conv] := 1;
                        end if;

                        if #AbelianInvariants(found_image) eq 5 then
                            break i;
                        else
                            continue i;
                        end if;
                    end if;
                end if;
            end for;
    
            error "miss";
        end for;
        
        //then search multiples of points lying near the singularity
        for i in [1..100] do
            vP1 := Desc`randptQ(Desc`singularity);
            vP2 := Desc`randpt();
            vP3 := Desc`randpt();
            PrintFile("auto_output.txt", Sprint([vP1, vP2, vP3]));

            D1 := Desc`DivFromPoints(vP1, vP2, vP3);
            mlst := AssociativeArray();
            mlst[1] := D1;
            D := D1;

            for k in Desc`ord_divs do
                _, mlst := Desc`find_mult(mlst, k);

                if k mod 2 eq 0 then
                    if Desc`IsTauAntiInv(mlst[k]) then
                        PrintFile("auto_output.txt", "Success at k= " cat Sprint(k));

                        Ddiv, mlst := Desc`find_mult(mlst, k div 2);
                        
                        try
                            sigma_vec, tau_vec := Desc`FindTwoTors(Ddiv);
                        catch e
                            print e;
                            continue i;
                        end try;

                        try
                            Qp_conv := Desc`LocalImageFromVecs(sigma_vec, tau_vec);
                        catch e
                            print e;
                            continue i;
                        end try;
                
                        found_image := sub<Desc`Hp6 | OrderedGenerators(found_image) cat [Qp_conv]>;
                        PrintFile("auto_output.txt", Sprint(#AbelianInvariants(found_image)) cat " " cat Sprint(Qp_conv));
                        if IsDefined(count, Qp_conv) then
                            count[Qp_conv] := count[Qp_conv] + 1;
                        else
                            count[Qp_conv] := 1;
                        end if;

                        if #AbelianInvariants(found_image) eq 6 then
                            break i;
                        else
                            continue i;
                        end if;
                    end if;
                end if;
            end for;
    
            error "miss";
        end for;
        
        for K in Keys(count) do
            PrintFile("auto_output.txt", "Number found of " cat Sprint(K) cat ": " cat Sprint(count[K]));
        end for;
        
    elif Desc`extension eq "ramified, anti-invariant" then
        count := AssociativeArray(Desc`Hp6);
        
        //first search multiples of random points
        for i in [1..100] do
            vP1 := Desc`randpt();
            vP2 := Desc`randpt();
            vP3 := Desc`randpt();
            PrintFile("auto_output.txt", Sprint([vP1, vP2, vP3]));

            D1 := Desc`DivFromPoints(vP1, vP2, vP3);
            mlst := AssociativeArray();
            mlst[1] := D1;
            D := D1;

            for k in Desc`ord_divs do
                _, mlst := Desc`find_mult(mlst, k);

                if k mod 2 eq 0 then
                    if Desc`IsAntiInv(mlst[k]) then
                        PrintFile("auto_output.txt", "Success at k= " cat Sprint(k));

                        Ddiv, mlst := Desc`find_mult(mlst, k div 2);
                        
                        try
                            sigma_vec, tau_vec := Desc`FindTwoTors(Ddiv);
                        catch e
                            print e;
                            continue i;
                        end try;

                        try
                            Qp_conv := Desc`LocalImageFromVecs(sigma_vec, tau_vec);
                        catch e
                            print e;
                            continue i;
                        end try;
                
                        found_image := sub<Desc`Hp6 | OrderedGenerators(found_image) cat [Qp_conv]>;
                        PrintFile("auto_output.txt", Sprint(#AbelianInvariants(found_image)) cat " " cat Sprint(Qp_conv));
                        if IsDefined(count, Qp_conv) then
                            count[Qp_conv] := count[Qp_conv] + 1;
                        else
                            count[Qp_conv] := 1;
                        end if;

                        if #AbelianInvariants(found_image) eq 5 then
                            break i;
                        else
                            continue i;
                        end if;
                    end if;
                end if;
            end for;
    
            error "miss";
        end for;
        
        //then search multiples of points lying near the singularity
        for i in [1..100] do
            vP1 := Desc`randptQ(Desc`singularity);
            vP2 := Desc`randpt();
            vP3 := Desc`randpt();
            PrintFile("auto_output.txt", Sprint([vP1, vP2, vP3]));

            D1 := Desc`DivFromPoints(vP1, vP2, vP3);
            mlst := AssociativeArray();
            mlst[1] := D1;
            D := D1;

            for k in Desc`ord_divs do
                _, mlst := Desc`find_mult(mlst, k);

                if k mod 2 eq 0 then
                    if Desc`IsAntiInv(mlst[k]) then
                        PrintFile("auto_output.txt", "Success at k= " cat Sprint(k));

                        Ddiv, mlst := Desc`find_mult(mlst, k div 2);
                        
                        try
                            sigma_vec, tau_vec := Desc`FindTwoTors(Ddiv);
                        catch e
                            print e;
                            continue i;
                        end try;

                        try
                            Qp_conv := Desc`LocalImageFromVecs(sigma_vec, tau_vec);
                        catch e
                            print e;
                            continue i;
                        end try;
                
                        found_image := sub<Desc`Hp6 | OrderedGenerators(found_image) cat [Qp_conv]>;
                        PrintFile("auto_output.txt", Sprint(#AbelianInvariants(found_image)) cat " " cat Sprint(Qp_conv));
                        if IsDefined(count, Qp_conv) then
                            count[Qp_conv] := count[Qp_conv] + 1;
                        else
                            count[Qp_conv] := 1;
                        end if;

                        if #AbelianInvariants(found_image) eq 6 then
                            break i;
                        else
                            continue i;
                        end if;
                    end if;
                end if;
            end for;
    
            error "miss";
        end for;
        
        for K in Keys(count) do
            PrintFile("auto_output.txt", "Number found of " cat Sprint(K) cat ": " cat Sprint(count[K]));
        end for;
        
    elif Desc`extension eq "bad on twist, invariant" then
        Cq := Desc`CurveFq;
        D0 := Desc`BaseDiv;
        
        for i in [1..100000] do
            vP1 := Desc`randpt();
            vP2 := Desc`randpt();
            vP3 := Desc`randpt();
            PrintFile("auto_output.txt", Sprint([vP1, vP2, vP3]));
            
            D1 := Divisor(Cq!vP1) + Divisor(Cq!vP2) + Divisor(Cq!vP3);
            mlst := AssociativeArray();
            mlst[1] := D1;
            
            for k in Desc`ord_divs do
                _, mlst := Desc`find_mult(mlst, k);
    
                if k mod 4 eq 0 then
                    if mlst[k] eq Desc`DivGroup!0 then
                        print "Success at k =", k;
                        Ddiv, mlst := Desc`find_mult(mlst, k div 4);
                        cand_sigma := Reduction(Ddiv - Desc`DivSigma(Ddiv), D0);
                        for T in Desc`TwoTorsion do
                            if Reduction(cand_sigma - T[1], D0) eq Desc`DivGroup!0 then
                                sigma_vec := T[2];
                            end if;
                        end for;
                
                        cand_tau, mlst := Desc`find_mult(mlst, k div 2);
                        for T in Desc`TwoTorsion do
                            if Reduction(cand_tau - T[1], D0) eq Desc`DivGroup!0 then
                                tau_vec := T[2];
                            end if;
                        end for;
            
                        Qp_conv := Desc`LocalImageFromVecs(sigma_vec, tau_vec);
                        found_image := sub<Desc`Hp6 | OrderedGenerators(found_image) cat [Qp_conv]>;
                        ab := #AbelianInvariants(found_image);
                        PrintFile("auto_output.txt", Sprint(ab) cat " " cat Sprint(Qp_conv));
                        
                        if #AbelianInvariants(found_image) eq 6 then
                            break i;
                        else
                            continue i;
                        end if;
                    end if;
                end if;
            end for;
        end for;

    elif Desc`extension eq "bad on twist, anti-invariant" then
        Cq := Desc`CurveFq;
        D0 := Desc`BaseDiv;
        
        for i in [1..100000] do
            vP1 := Desc`randpt();
            vP2 := Desc`randpt();
            vP3 := Desc`randpt();
            PrintFile("auto_output.txt", Sprint([vP1, vP2, vP3]));
            
            D1 := Divisor(Cq!vP1) + Divisor(Cq!vP2) + Divisor(Cq!vP3);
            mlst := AssociativeArray();
            mlst[1] := D1;
            
            for k in Desc`ord_divs do
                _, mlst := Desc`find_mult(mlst, k);
    
                if k mod 4 eq 0 then
                    if mlst[k] eq Desc`DivGroup!0 then
                        print "Success at k =", k;
                        Ddiv, mlst := Desc`find_mult(mlst, k div 4);
                        cand_sigma := Reduction(Ddiv + Desc`DivSigma(Ddiv), D0);
                        for T in Desc`TwoTorsion do
                            if Reduction(cand_sigma - T[1], D0) eq Desc`DivGroup!0 then
                                sigma_vec := T[2];
                            end if;
                        end for;
                
                        cand_tau, mlst := Desc`find_mult(mlst, k div 2);
                        for T in Desc`TwoTorsion do
                            if Reduction(cand_tau - T[1], D0) eq Desc`DivGroup!0 then
                                tau_vec := T[2];
                            end if;
                        end for;
            
                        Qp_conv := Desc`LocalImageFromVecs(sigma_vec, tau_vec);
                        found_image := sub<Desc`Hp6 | OrderedGenerators(found_image) cat [Qp_conv]>;
                        ab := #AbelianInvariants(found_image);
                        PrintFile("auto_output.txt", Sprint(ab) cat " " cat Sprint(Qp_conv));
                        
                        if #AbelianInvariants(found_image) eq 6 then
                            break i;
                        else
                            continue i;
                        end if;
                    end if;
                end if;
            end for;
        end for;
    else
        error "extension incorrectly defined";
    end if;
    
    [Eltseq(Desc`Hp6!a) : a in OrderedGenerators(found_image)];
    PrintFile("auto_output.txt", Sprint([Eltseq(Desc`Hp6!a) : a in OrderedGenerators(found_image)]));
    
    if p eq 2 then
        assert #AbelianInvariants(found_image) eq 9;
    else
        assert #AbelianInvariants(found_image) eq 6;
    end if;
    
    selmer_candidate:=(found_image@@HS6toHp6) meet selmer_candidate;
    PrintFile("auto_output.txt", "Current rank of selmer candidate: " cat Sprint(#AbelianInvariants(selmer_candidate)));
    
    polynomial_map1 := func<a | &+[Desc`projHp[i](a)*ZZ!proj_vec1[i] : i in [1..6]]>;
    component_map1 := hom<Desc`Hp6->Desc`Hp | [polynomial_map1(a): a in OrderedGenerators(Desc`Hp6)]>;
    polynomial_map2 := func<a | &+[Desc`projHp[i](a)*ZZ!proj_vec2[i] : i in [1..6]]>;
    component_map2 := hom<Desc`Hp6->Desc`Hp | [polynomial_map2(a): a in OrderedGenerators(Desc`Hp6)]>;
    polynomial_map3 := func<a | &+[Desc`projHp[i](a)*ZZ!proj_vec3[i] : i in [1..6]]>;
    component_map3 := hom<Desc`Hp6->Desc`Hp | [polynomial_map3(a): a in OrderedGenerators(Desc`Hp6)]>;

    Hp3,embHp3,projHp3:=DirectSum([Desc`Hp: i in [1..3]]);
    projection_map := func< a | &*[embHp3[1](component_map1(a)), embHp3[2](component_map2(a)), embHp3[3](component_map3(a))]>;
    Hp6toHp3 := hom<Desc`Hp6->Hp3 | [projection_map(a): a in OrderedGenerators(Desc`Hp6)]>;
    
    projected_image := Hp6toHp3(found_image);
    
    proj_procedural_map:=func< a | &*[embHp3[i](HStoHp(projHS3[i](a))) : i in [1..3]]>;
    HS3toHp3 := hom<HS3->Hp3 | [proj_procedural_map(a): a in OrderedGenerators(HS3)]>;
    
    proj_selmer_candidate := (projected_image@@HS3toHp3) meet proj_selmer_candidate;
    PrintFile("auto_output.txt", "Current rank of projected selmer candidate: " cat Sprint(#AbelianInvariants(proj_selmer_candidate)));
    PrintFile("auto_output.txt", Sprint("-----------------------------------------------"));
end for;

PrintFile("auto_output.txt", "p = " cat Sprint(-1));

RR := RealField();
PolyRR := PolynomialRing(RR); xRR := PolyRR.1;
ContactPoints:=[[Evaluate(v, [r[1],1]) : v in bt[2]]: r in Roots(Evaluate(bt[1],[xRR,1])), bt in btr`ContactPoints];
ContactPoints:=[[v/m: v in C] where m:=Maximum([Abs(a): a in C]): C in ContactPoints];

HR := AbelianGroup([2]);
RRtoHR := func<r | Sign(r) eq 1 select HR!0 else HR!1>;
HR6, embHR, projHR := DirectSum([HR : i in [1..6]]);
HStoHR:=hom<HS->HR| [RRtoHR(g@@QtoHS): g in OrderedGenerators(HS)]>;
procedural_map:=func< a | &*[embHR[i](HStoHR(projHS[i](a))) : i in [1..6]]>;
HS6toHR6:=hom<HS6->HR6| [procedural_map(a): a in OrderedGenerators(HS6)]>;

if -1 in d_div then
    input := Read("sage-output.txt");
    basis := eval(input);
    found_image := sub<HR6 | [HR6!b : b in basis]>;
else
    found_image := sub<HR6 | >;

    for cp in [1..28] do
        images := [];
        for i in [1..7] do
            v := RR!bitang_eval[i][cp];
            if v eq RR!0 then
                for triple in btr`UsefulTriples[i] do
                    v := &*[RR!bitang_eval[k][cp] : k in triple[1]];
                    if v ne RR!0 then
                        break triple;
                    end if;
                end for;
            end if;
            if v eq RR!0 then
                print "skip";
                continue cp;
            end if;
            Append(~images, v);
        end for;
        w := [RRtoHR(n) : n in images];
        w_div := [w[j] - w[1] : j in [2..7]];
        image := &+[embHR[i](w_div[i]) : i in [1..6]];
        if not(image in found_image) then
            found_image := sub<HR6 | OrderedGenerators(found_image) cat [image]>;
        end if;
        ab := #AbelianInvariants(found_image);
        PrintFile("auto_output.txt", Sprint(ab));
    end for;
end if;

PrintFile("auto_output.txt", Sprint([Eltseq(HR6!a) : a in OrderedGenerators(found_image)]));

selmer_candidate:=(found_image@@HS6toHR6) meet selmer_candidate;
PrintFile("auto_output.txt", "Rank of 2-Selmer group: " cat Sprint(#AbelianInvariants(selmer_candidate)));

polynomial_map1 := func<a | &+[projHR[i](a)*ZZ!proj_vec1[i] : i in [1..6]]>;
component_map1 := hom<HR6->HR | [polynomial_map1(a): a in OrderedGenerators(HR6)]>;
polynomial_map2 := func<a | &+[projHR[i](a)*ZZ!proj_vec2[i] : i in [1..6]]>;
component_map2 := hom<HR6->HR | [polynomial_map2(a): a in OrderedGenerators(HR6)]>;
polynomial_map3 := func<a | &+[projHR[i](a)*ZZ!proj_vec3[i] : i in [1..6]]>;
component_map3 := hom<HR6->HR | [polynomial_map3(a): a in OrderedGenerators(HR6)]>;

polynomial_map4 := func<a | &+[projHR[i](a)*ZZ!proj_vec4[i] : i in [1..6]]>;
component_map4 := hom<HR6->HR | [polynomial_map4(a): a in OrderedGenerators(HR6)]>;
polynomial_map5 := func<a | &+[projHR[i](a)*ZZ!proj_vec5[i] : i in [1..6]]>;
component_map5 := hom<HR6->HR | [polynomial_map5(a): a in OrderedGenerators(HR6)]>;
polynomial_map6 := func<a | &+[projHR[i](a)*ZZ!proj_vec6[i] : i in [1..6]]>;
component_map6 := hom<HR6->HR | [polynomial_map6(a): a in OrderedGenerators(HR6)]>;

HR3,embHR3,projHR3:=DirectSum([HR: i in [1..3]]);
projection_map := func< a | &*[embHR3[1](component_map1(a)), embHR3[2](component_map2(a)), embHR3[3](component_map3(a))]>;
projection_map2 := func< a | &*[embHR3[1](component_map4(a)), embHR3[2](component_map5(a)), embHR3[3](component_map6(a))]>;
HR6toHR3 := hom<HR6->HR3 | [projection_map(a): a in OrderedGenerators(HR6)]>;
HR6toHR3_2 := hom<HR6->HR3 | [projection_map2(a): a in OrderedGenerators(HR6)]>;
    
projected_image := HR6toHR3(found_image);
projected_image2 := HR6toHR3_2(found_image);
    
proj_procedural_map:=func< a | &*[embHR3[i](HStoHR(projHS3[i](a))) : i in [1..3]]>;
HS3toHR3 := hom<HS3->HR3 | [proj_procedural_map(a): a in OrderedGenerators(HS3)]>;
    
proj_selmer_candidate := (projected_image@@HS3toHR3) meet proj_selmer_candidate;
proj_selmer_candidate2 := (projected_image2@@HS3toHR3) meet proj_selmer_candidate2;
PrintFile("auto_output.txt", "Rank of 2-isogeny-Selmer group: " cat Sprint(#AbelianInvariants(proj_selmer_candidate)));