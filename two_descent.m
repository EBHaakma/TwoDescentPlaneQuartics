DescentFunc := recformat<curve, singularity, extension, ord_divs, Hp, QptoHp, Hp6, embHp, projHp, randpt, randptQ, IsGalInv, IsSigmaAntiInv, IsTauAntiInv, IsAntiInv, IsZr, find_mult, FindTwoTors, LocalImageFromVecs, DivFromPoints, PQp, ContactPoints, TwoTorsion, FourTorsion, DivSigma, CurveFq, DivGroup, BaseDiv>;

function InitDescentFunc(btr, p, Delta)
    C:=Curve(Proj(Parent(btr`f)),btr`f);
    rational_points:=&join[Support(Scheme(C,l)): l in btr`bitangs];
    search := false;
    if rational_points eq {} then
        rational_points := Seqset(PointSearch(C, 10000));
        search := true;
    end if;
    bad_primes := [F[1] : F in Factorization(Numerator(DixmierOhnoInvariants(C)[13]))];

    
    Zp := pAdicRing(p, 50);
    Qp := pAdicField(p, 50);
    PZp<x> := PolynomialRing(Zp);
    if p ne 2 then
        assert exists(nqr){a: a in [1..p-1] | LegendreSymbol(a,p) eq -1};
        a := nqr;
        Unram<alpha> := ext<Zp | x^2 - a>;
        PUnram<xU> := PolynomialRing(Unram);
        Ram<beta> := ext<Unram | xU^2 - p>;
        function tau(z)
            z := Ram!z;
            coeff := Coefficients(z);
            newCoeff := [coeff[1], -coeff[2]];
            return ChangePrecision(Ram!newCoeff, AbsolutePrecision(z));
        end function;

        alpha_imag := Trace(alpha) - alpha;

        function sigma(z)
            z := Ram!z;
            coeffBeta := Coefficients(z);
            coeffReal := Coefficients(coeffBeta[1]);
            coeffImag := Coefficients(coeffBeta[2]);
            newCoeff := [coeffReal[1] + coeffReal[2]*alpha_imag, coeffImag[1] + coeffImag[2]*alpha_imag];
            return ChangePrecision(Ram!newCoeff, AbsolutePrecision(z));;
        end function;
    end if;
    f := btr`f;
    
    if p ne 2 then
        if not p in bad_primes then
            if LegendreSymbol(Delta div p, p) eq 1 then
                extension := "bad on twist, invariant";
            elif LegendreSymbol(Delta div p, p) eq -1 then
                extension := "bad on twist, anti-invariant";
            else
                error "p^2 divides Delta";
            end if;
        elif LegendreSymbol(Delta, p) eq 0 then
            if LegendreSymbol(Delta div p, p) eq 1 then
                extension := "ramified, invariant";
            elif LegendreSymbol(Delta div p, p) eq -1 then
                extension := "ramified, anti-invariant";
            end if;
        elif LegendreSymbol(Delta, p) eq -1 then
            extension := "unramified";
        elif LegendreSymbol(Delta, p) eq 1 then
            extension := "no extension";
        end if;
    else
        extension := "no extension";
    end if;
    
    print extension;
    
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

    if extension eq "no extension" then
        if IsEmpty(rational_points) then
            PQp<yQp> := PolynomialRing(Qp);

            function randompointQp()
                repeat
                    x0 := Qp!Random([-p^2..p^2]);
                    roots := Roots(Evaluate(btr`f, [x0, yQp, 1]));
                until not (roots eq []);
                y0 := Random(roots)[1];
                vP := [x0, y0, Qp!1];
                return vP;
            end function;
            
            P := randompointQp();
            
            //repeat
                //Pt := randompointFp();
                //roots := Roots(Evaluate(btr`f, <Qp!Pt[1], yQp, Qp!Pt[3]>));
            //until not (roots eq []);
            //y0 := Random(roots)[1];
            //Pt := [Qp!Pt[1], y0, Qp!Pt[3]];
            //minval := Minimum([Valuation(Elt) : Elt in Pt]);
            //if minval lt 0 then
                //Pt := [p^(-minval)*Elt : Elt in Pt];
            //end if;
            //Pt_p := [GF(p)!Elt : Elt in Eltseq(Pt)];
            //P := Pt;
        else
            P := Representative(rational_points);
        end if;
        PonQp := [Qp!a : a in Eltseq(P)];
        
        Hp, QptoHp := pSelmerGroup(2,Qp);
        Hp6,embHp,projHp:=DirectSum([Hp: i in [1..6]]);
        
        RQp:=PolynomialRing(Qp); sQp:=RQp.1;
        P2:=ProjectiveSpace(Rationals(),2);
        ContactPoints:=[];
        for V in btr`ContactPoints do
            if Evaluate(V[1],[1,0]) eq 0 then
                Append(~ContactPoints,[Evaluate(v,[Zp|1,0]): v in V[2]]);
            end if;
            for r in Roots(Evaluate(V[1],[sQp,1])) do
                v:=Min(0,Valuation(r[1]));
                st:=[Zp|p^(-v)*r[1],p^(-v)];
                Append(~ContactPoints,[Evaluate(v,st): v in V[2]]);
            end for;
        end for;
        
        ContactPoints:=[ [Zp|a*scl: a in v] where scl:=p^(-Minimum([Valuation(c): c in v])) where v:=Eltseq(P): P in ContactPoints];
        return rec<DescentFunc | extension := extension, Hp := Hp, QptoHp := QptoHp, 
            Hp6 := Hp6, embHp := embHp, projHp := projHp, PQp := PonQp, ContactPoints := ContactPoints>;
    
    elif extension eq  "bad on twist, invariant" or extension eq "bad on twist, anti-invariant" then
        Fp:=GF(p);
        PFp<xf> := PolynomialRing(Fp);
        Fq:=ext<Fp | xf^2 - a>;
        Pf<Xf,Yf,Zf> := PolynomialRing(Fq,3);
        PFp<yf> := PolynomialRing(Fq);
        P2<x,y,z>:=ProjectiveSpace(Fq,2);
        Cq:=Curve(P2,Evaluate(f,[x,y,z]));
        Pfp3<Xp, Yp, Zp> := PolynomialRing(Fp,3);
        P2p<xp, yp, zp> := ProjectiveSpace(Fp,2);
        Cp := Curve(P2p,Evaluate(f,[xp,yp,zp]));
        
        if IsEmpty(rational_points) then
            function randompointFp()
                repeat
                    x0 := GF(p)!Random([1..p]);
                    roots := Roots(Evaluate(btr`f, [x0, xf, 1]));
                until not (roots eq []);
                y0 := Random(roots)[1];
                vP := [x0, y0, GF(p)!1];
                return vP;
            end function;
            
            PQp<yQp> := PolynomialRing(Qp);
            repeat
                Pt := randompointFp();
                roots := Roots(Evaluate(btr`f, <Qp!Pt[1], yQp, Qp!Pt[3]>));
            until not (roots eq []);
            y0 := Random(roots)[1];
            Pt := [Qp!Pt[1], y0, Qp!Pt[3]];
            minval := Minimum([Valuation(Elt) : Elt in Pt]);
            if minval lt 0 then
                Pt := [p^(-minval)*Elt : Elt in Pt];
            end if;
            Pt_p := [GF(p)!Elt : Elt in Eltseq(Pt)];
            P := Pt;
        else
            P := Representative(rational_points);
        end if;
        P0 := Cq![Fp!Elt : Elt in Eltseq(P)];
        
        DivGroup := DivisorGroup(Cq);
        D0 := Divisor(P0);
        
        function randompointFq()
            repeat
                x0 := Fq![Random([1..p]) : i in [1..2]];
                roots := Roots(Evaluate(f, [x0, yf, 1]));
            until not (roots eq []);
            y0 := Random(roots)[1];
            vP := [x0, y0, Fq!1];
            return vP;
        end function;
        
        sigma:=hom<Parent(x)->Parent(x) | map<Fq->Fq | a:->Frobenius(a)>, [x,y,z]>;
        sigma_effective_div:=func<D| Divisor(Cq,ideal<Parent(x)|[sigma(g): g in Basis(Ideal(D))]>)>;
        sigma_div:=func< D| sigma_effective_div(Numerator(D))-sigma_effective_div(Denominator(D))>;
        
        B := [<Evaluate(Pf!btr`bitangs[i], <x,y,z>), BitangentLabeling[i]> : i in [1..#btr`bitangs]];
        f_proj := Evaluate(Pf!btr`f, <x,y,z>);
        D_lst := [<Divisor(Cq, Radical(ideal<Parent(x)|f_proj, b[1]>)), b[2]> : b in B];
        D_lst := [(Degree(D[1]) eq 2) select D else <2*D[1], D[2]>: D in D_lst];
        two_tors_lst := &cat[[<D1[1] - D2[1], D1[2] - D2[2]> : D1 in D_lst] : D2 in D_lst];
        
        assert &and[Degree(T[1]) eq 0 : T in two_tors_lst];
        
        //we construct a large list of two torsion points that includes duplicates, then use the below code to prune it
        
        two_tors_split := [];
        done := [];
        for T1 in two_tors_lst do
            if T1[2] in done then
                continue T1;
            end if;
            split_lst := [];
            for T2 in two_tors_lst do
                if T1[2] eq T2[2] then
                    assert IsLinearlyEquivalent(T1[1], T2[1]);
                    Append(~split_lst, T2);
                end if;
            end for;
            Append(~done, T1[2]);
            Append(~two_tors_split, split_lst);
        end for;
        
        two_tors_lst := [Representative(S) : S in two_tors_split];
        
        grp_ord := Evaluate(LPolynomial(Cp,2), 1);
        ord_divs := Divisors(2*grp_ord);
        print ord_divs;
        
        function find_mult(lst, i)
            if IsDefined(lst, i) then
                return lst[i], lst;
            else
                if i mod 2 eq 0 then
                    _, lst := find_mult(lst, i div 2);
                    lst[i] := Reduction(lst[i div 2] + lst[i div 2], D0);
                    return lst[i], lst;
                else
                    _, lst := find_mult(lst, i div 2);
                    _, lst := find_mult(lst, (i div 2) + 1);
                    lst[i] := Reduction(lst[i div 2] + lst[(i div 2)+1], D0);
                    return lst[i], lst;
                end if;
            end if;
        end function;
            
        Hp, QptoHp := pSelmerGroup(2,Qp);
        Hp6,embHp,projHp:=DirectSum([Hp: i in [1..6]]);

        function weil_pairing(A, B)
            return A[1]*B[6]+A[2]*B[5]+A[3]*B[4]+A[4]*B[3]+A[5]*B[2]+A[6]*B[1];
        end function;

        function LocalImageFromVecs(s_vec, t_vec)
            Qp_conv := Hp6!0;
            for i in [1..6] do
                if weil_pairing(B[i+1][2] - B[1][2], s_vec) eq 0 then
                    if weil_pairing(B[i+1][2] - B[1][2], t_vec) eq 0 then
                        Qp_conv := Qp_conv + embHp[i](QptoHp(1));
                    elif weil_pairing(B[i+1][2] - B[1][2], t_vec) eq 1 then
                        Qp_conv := Qp_conv + embHp[i](QptoHp(p));
                    else
                        error "Weil pairing error";
                    end if;
                elif weil_pairing(B[i+1][2] - B[1][2], s_vec) eq 1 then
                    if weil_pairing(B[i+1][2] - B[1][2], t_vec) eq 0 then
                        Qp_conv := Qp_conv + embHp[i](QptoHp(a));
                    elif weil_pairing(B[i+1][2] - B[1][2], t_vec) eq 1 then
                        Qp_conv := Qp_conv + embHp[i](QptoHp(p*a));
                    else
                        error "Weil pairing error";
                    end if;
                else
                    error "Weil pairing error";
                end if;
            end for;
            return Qp_conv;
        end function;
        
        return rec<DescentFunc | curve := C, extension := extension, ord_divs := ord_divs, Hp := Hp, QptoHp := QptoHp, Hp6 := Hp6, 
            embHp := embHp, projHp := projHp, randpt := randompointFq, find_mult := find_mult, 
            LocalImageFromVecs := LocalImageFromVecs, TwoTorsion := two_tors_lst, DivSigma := sigma_div, 
            CurveFq := Cq, DivGroup := DivGroup, BaseDiv := D0>;
        
    else
        FinP2<Xm, Ym, Zm> := ProjectiveSpace(GF(p), 2);
        Cp := BaseChange(C, FinP2);
        Q := SingularPoints(Cp)[1];
        print Q;
        ratpts_p := [[GF(p)!Elt : Elt in Eltseq(Pt)] : Pt in Setseq(rational_points) 
                            | Denominator(Pt[1]) mod p ne 0 and Denominator(Pt[2]) mod p ne 0];
                            
        P_found := false;
        for Pt in Setseq(rational_points) do
            if Denominator(Pt[1]) mod p ne 0 and Denominator(Pt[2]) mod p ne 0 then
                Pt_p := [GF(p)!Elt : Elt in Eltseq(Pt)];
                if Pt_p ne Eltseq(Q) then
                    if #[Pt2 : Pt2 in ratpts_p | Pt2 eq Pt_p] eq 1 or search eq true then
                        P := Pt;
                        P_found := true;
                        break Pt;
                    end if;
                end if;
            end if;
        end for;
        
        if not P_found then
            PFp<yf> := PolynomialRing(GF(p));

            function randompointFp()
                repeat
                    x0 := GF(p)!Random([1..p]);
                    roots := Roots(Evaluate(btr`f, [x0, yf, 1]));
                until not (roots eq []);
                y0 := Random(roots)[1];
                vP := [x0, y0, GF(p)!1];
                return vP;
            end function;
            
            PQp<yQp> := PolynomialRing(Qp);
            repeat
                repeat
                    Pt := randompointFp();
                    roots := Roots(Evaluate(btr`f, <Qp!Pt[1], yQp, Qp!Pt[3]>));
                until not (roots eq []);
                y0 := Random(roots)[1];
                Pt := [Qp!Pt[1], y0, Qp!Pt[3]];
                minval := Minimum([Valuation(Elt) : Elt in Pt]);
                if minval lt 0 then
                    Pt := [p^(-minval)*Elt : Elt in Pt];
                end if;
                Pt_p := [GF(p)!Elt : Elt in Eltseq(Pt)];
            until Pt_p ne Eltseq(Q);
            P := Pt;
        end if;
        
        Uni := InitArithFunc(f, p, Ram, P, 8, 2);
        R:=Parent(f);
        k:=BaseRing(R);
        P2<X,Y,Z>:=Proj(R);
        UniQp := InitArithFunc(f, p, Zp, P, 8, 2);
        
        Hp, QptoHp := pSelmerGroup(2,Qp);
        Hp6,embHp,projHp:=DirectSum([Hp: i in [1..6]]);
        
        bts := btr`bitangs;
        bts_basis := bts[1..7];
        P2 := AmbientSpace(ReducedSubscheme(Scheme(C,bts[1])));
        polys := [DefiningPolynomials(Image(IdentityMap(P2),ReducedSubscheme(Scheme(C,l)),2)): l in bts];
        mon:=[MonomialsOfDegree(Parent(f),d): d in [1..8]];
        bts_mats := [PseudoEchelonForm(Matrix([[Qp!MonomialCoefficient(Parent(f)!p, m) : m in mon[2]] : p in poly])) :  poly in polys];
        
        //if Type(Parent(P[1])) eq FldRat then
            //lcm:=LCM([Denominator(c) : c in Eltseq(P)]);
            //v:=[c*lcm : c in Eltseq(P)];
            //v:=[R!elt : elt in v];
            //assert Evaluate(f,v) eq 0;
            //IP:=[v[2]*X-v[1]*Y,v[3]*X-v[1]*Z,v[2]*Z-v[3]*Y];
            //MP_1, MP_1pivs:=PseudoEchelonForm(Matrix([[Zp!MonomialCoefficient(g, m) : m in [X, Y, Z]]: g in IP]));
        //else
            //v := [Qp!elt : elt in P];
            //PolyQpRng<XQp, YQp, ZQp> := PolynomialRing(Qp, 3);
            //fQp := PolyQpRng!ChangeRing(f, Qp);
            //test := Evaluate(fQp, v);
            //assert test eq BigO(Qp!p^Minimum(AbsolutePrecision(test), 50));
            //IP := [v[2]*XQp - v[1]*YQp, v[3]*XQp - v[1]*ZQp, v[2]*ZQp - v[3]*YQp];
            //Wp := RModule(Qp, #MonomialsOfDegree(PolyQpRng, 1));
            //veclst := [Wp![MonomialCoefficient(g, m) : m in MonomialsOfDegree(PolyQpRng, 1)] : g in IP];
            //MP_1, MP_1pivs := PseudoEchelonForm(Matrix(veclst));
        //end if;
        MP_1 := Uni`Pmat;
        W := RModule(Zp, #mon[1]);
        MP_2 := PseudoEchelonForm(UniQp`mul(MP_1, Matrix(Basis(W))));
        
        bts_divs := [<NewDiv(PseudoEchelonForm(UniQp`mul(MP_2, bts_mats[i]))), BitangentLabeling[i]> : i in [1..7]];
        neg_div0 := UniQp`neg(bts_divs[1][1]);
        tors_basis := [<UniQp`sum(bitang[1], neg_div0), bitang[2] - bts_divs[1][2]> : bitang in bts_divs[2..7]];
        
        LinComs:=[<UniQp`Zr,VecF2!0>];
        for i in [1..6] do
            LinComs :=LinComs cat [<UniQp`sum(a[1],tors_basis[i][1]),a[2]+tors_basis[i][2]>: a in LinComs];
        end for;
    
        LinComs:=[<(assigned D[1]`mat) select 
            NewDiv(D[1]`mat : negmat:= D[1]`mat)
            else NewDiv(D[1]`negmat :negmat:= D[1]`negmat),D[2]>: D in LinComs];
            
        LinComsRam := [<NewDiv(ChangeRing(T[1]`mat, Ram): negmat:= ChangeRing(T[1]`negmat, Ram)), T[2]>: T in LinComs ];
        
        LCp:=[<EchelonForm(ChangeRing(r[1]`mat,GF(p))),r[2]>: r in LinComs];
        U:=[ [b[2]: b in LCp | b[1] eq a] : a in {a[1]: a in LCp}];
        assert #{u[1]-u[2]: u in U | #u eq 2 } eq 1;
        v := [u[1]-u[2]: u in U | #u eq 2][1];
        DoubleDivs := &cat[u : u in U | #u eq 2];
        
        for L in LinComsRam do
            if L[2] eq v then
                T0 := L;
            end if;
        end for;
        
        UnramF<alphaF> := FieldOfFractions(Unram);
        RamF<betaF> := FieldOfFractions(Ram);
        R2<x1,y1>:=PolynomialRing(Rationals(),2);
        f_dehom := Evaluate(f,<x1, y1, 1>);
        R3<yR> := PolynomialRing(RamF);
        RamR<XR, YR, ZR> := PolynomialRing(RamF, 3);
        monR:=[MonomialsOfDegree(RamR, d) : d in [1..8]];
        
        if extension eq "unramified" then
            invp := AbelianInvariants(ClassGroup(ChangeRing(Curve(P2, f), GF(p))));
            grp_ord := LCM([invp[i] : i in [1..#invp - 1]]);
        else
            invp2 := AbelianInvariants(ClassGroup(ChangeRing(Curve(P2, f), GF(p^2))));
            grp_ord := LCM([invp2[i] : i in [1..#invp2 - 1]]);
        end if;
        FinPoly2<xm, ym> := PolynomialRing(GF(p), 2);
        fp := DefiningPolynomial(Cp);
        fpt := Evaluate(fp, <Xm + Q[1]*Zm, Ym + Q[2]*Zm, Zm>);
        Cpt := Curve(FinP2, fpt);
        TCoeffs := [MonomialCoefficient(Evaluate(DefiningPolynomial(TangentCone(Cpt, Cpt![0,0,1])), <xm, ym, 1>), m) : m in <xm^2, xm*ym, ym^2>];
        
        if extension eq "unramified" then
            if LegendreSymbol(Integers()!(TCoeffs[2]^2 - 4*TCoeffs[1]*TCoeffs[3]), p) eq 1 then
                grp_ord := grp_ord*(p-1);
            elif LegendreSymbol(Integers()!(TCoeffs[2]^2 - 4*TCoeffs[1]*TCoeffs[3]), p) eq -1 then
                grp_ord := grp_ord*(p+1);
            else
                error "Discriminant divisible by p";
            end if;
        else
            grp_ord := grp_ord*(p-1)*(p+1);
        end if;
        ord_divs := Divisors(2*grp_ord);
        print ord_divs;
        
        divsum := Uni`sum;
        IsGalInv := Uni`IsGalInv;
        IsSigmaAntiInv := Uni`IsSigmaAntiInv;
        IsTauAntiInv := Uni`IsTauAntiInv;
        IsAntiInv := Uni`IsAntiInv;
        IsZr := Uni`IsZr;
        
        function find_mult(lst, i)
            if IsDefined(lst,i) then
                return lst[i],lst;
            else
                if i mod 2 eq 0 then
                    _,lst:=find_mult(lst, i div 2);
                    lst[i], lst[i div 2], lst[i div 2] := divsum(lst[i div 2], lst[i div 2]);
                    return lst[i],lst;
                elif i mod 2 eq 1 then
                    _,lst:=find_mult(lst, i div 2);
                    _,lst:=find_mult(lst, (i div 2)+1);
                    lst[i], lst[i div 2], lst[(i div 2) + 1] := divsum(lst[i div 2], lst[(i div 2) + 1]);
                    return lst[i],lst;
                else
                    error "This should not happen";
                end if;
            end if;
        end function;
        
        function randompoint()
            repeat
                x0 := Ram![Unram![Random([-p^2..p^2]): i in [1..2]]: j in [1..2]];
                roots := Roots(Evaluate(f_dehom, [x0, yR]));
            until not (roots eq []);
            y0:=roots[1][1];
            vP1 := [x0, y0, Ram!1];
            return vP1;
        end function;

        resRam<ar>, resmap := ResidueClassField(Ram);
        
        function ChangePrecisionMatrix(A, prec)
            assert &and[AbsolutePrecision(a) ge prec : a in Eltseq(A)];
            return Matrix(BaseRing(A), Nrows(A), Ncols(A), [ChangePrecision(a, prec) : a in Eltseq(A)]);
        end function;
        
        function weil_pairing(A, B)
            return A[1]*B[6]+A[2]*B[5]+A[3]*B[4]+A[4]*B[3]+A[5]*B[2]+A[6]*B[1];
        end function;
        
        function randomPointAboveQ(Q)
            Q_lst := Eltseq(Q);
            breakCond := false;
            repeat
                j1 := Random([-p^2..p^2]);
                j2 := Random([-p^2..p^2]);
                j3 := Random([-p^2..p^2]);
                j4 := Random([-p^2..p^2]);
                x0 := Ram!Q[1] + Ram!j1*p + Ram!j2*p*alpha + Ram!j3*beta + Ram!j4*alpha*beta;
                roots := Roots(Evaluate(f_dehom, [x0, yR]));
                if not (roots eq []) then
                    for r in roots do
                        if ChangePrecision(r[1], 1) eq ChangePrecision(Ram!Q[2], 1) then
                            y0 := r[1];
                            breakCond := true;
                        end if;
                    end for;
                end if;
            until breakCond;
            vP := [x0, y0, 1];
            return vP;
        end function;
        
        function FindEqualTwoTorsion(D)
            Ddiv := D;
            E_sigma := rec<Div |>;
            E_tau := rec<Div |>;
            
            //we will construct divisors E_sigma and E_tau such that D + E_sigma and D+E_tau are two-torsion

            if extension eq "unramified" then
                //here, Delta is anti-invariant under sigma and invariant under tau
                //thus, the same is true for 2D
                //in our Weil restriction paper, we have sigma in Gal(L) and tau in Gal(k) \ Gal(L)
                //as such, we need E_sigma = sigma(D) and E_tau = -tau(D)
                if assigned Ddiv`mat then
                    E_sigma`mat := Matrix(Ram, Nrows(Ddiv`mat), Ncols(Ddiv`mat), [sigma(m) : m in Eltseq(Ddiv`mat)]);
                    E_tau`negmat := Matrix(Ram, Nrows(Ddiv`mat), Ncols(Ddiv`mat), [tau(m) : m in Eltseq(Ddiv`mat)]);
                end if;

                if assigned Ddiv`negmat then
                    E_sigma`negmat := Matrix(Ram, Nrows(Ddiv`negmat), Ncols(Ddiv`negmat), [sigma(m) : m in Eltseq(Ddiv`negmat)]);
                    E_tau`mat := Matrix(Ram, Nrows(Ddiv`negmat), Ncols(Ddiv`negmat), [tau(m) : m in Eltseq(Ddiv`negmat)]);
                end if;
            elif extension eq "ramified, invariant" then
                //here, Delta is invariant under sigma and anti-invariant under tau
                //thus, the same is true for 2D
                //in our Weil restriction paper, we have sigma in Gal(k) \ Gal(L) and tau in Gal(L)
                //we need E_sigma = -sigma(D) and E_tau = tau(D)
                if assigned Ddiv`mat then
                    E_sigma`negmat := Matrix(Ram, Nrows(Ddiv`mat), Ncols(Ddiv`mat), [sigma(m) : m in Eltseq(Ddiv`mat)]);
                    E_tau`mat := Matrix(Ram, Nrows(Ddiv`mat), Ncols(Ddiv`mat), [tau(m) : m in Eltseq(Ddiv`mat)]);
                end if;

                if assigned Ddiv`negmat then
                    E_sigma`mat := Matrix(Ram, Nrows(Ddiv`negmat), Ncols(Ddiv`negmat), [sigma(m) : m in Eltseq(Ddiv`negmat)]);
                    E_tau`negmat := Matrix(Ram, Nrows(Ddiv`negmat), Ncols(Ddiv`negmat), [tau(m) : m in Eltseq(Ddiv`negmat)]);
                end if;
            elif extension eq "ramified, anti-invariant" then
                //here, Delta is anti-invariant under both sigma and tau
                //thus, the same is true for 2D
                //in our Weil restriction paper, we have sigma and tau both in Gal(k) \ Gal(L)
                //we need E_sigma = sigma(D) and E_tau = tau(D)
                if assigned Ddiv`mat then
                    E_sigma`mat := Matrix(Ram, Nrows(Ddiv`mat), Ncols(Ddiv`mat), [sigma(m) : m in Eltseq(Ddiv`mat)]);
                    E_tau`mat := Matrix(Ram, Nrows(Ddiv`mat), Ncols(Ddiv`mat), [tau(m) : m in Eltseq(Ddiv`mat)]);
                end if;

                if assigned Ddiv`negmat then
                    E_sigma`negmat := Matrix(Ram, Nrows(Ddiv`negmat), Ncols(Ddiv`negmat), [sigma(m) : m in Eltseq(Ddiv`negmat)]);
                    E_tau`negmat := Matrix(Ram, Nrows(Ddiv`negmat), Ncols(Ddiv`negmat), [tau(m) : m in Eltseq(Ddiv`negmat)]);
                end if;
            end if;

            tors_div_sigma, Ddiv, E_sigma := divsum(Ddiv, E_sigma);
            tors_div_tau, Ddiv, E_tau := divsum(Ddiv, E_tau);

            sigma_lst := [tors_div_sigma];
            tau_lst := [tors_div_tau];

            for T in LinComsRam do
                if assigned tors_div_sigma`mat then
                    if ChangeRing(ChangeRing(tors_div_sigma`mat, Ram), resmap) eq ChangeRing(T[1]`mat, resmap) then
                        if T[2] in DoubleDivs then
                            psigma, sigma_list := find_mult(sigma_lst, p);

                            for L in LinComsRam do
                                if L[2] eq T[2] + T0[2] then
                                    TpT0 := L;
                                end if;
                            end for;

                            if assigned psigma`mat then
                                if ChangePrecisionMatrix(ChangeRing(psigma`mat, Ram), 3) eq ChangePrecisionMatrix(T[1]`mat, 3) then
                                    sigma_vec := T[2];
                                    print "Sigma Equality to T", sigma_vec;
                                elif ChangePrecisionMatrix(ChangeRing(psigma`mat, Ram), 3) eq ChangePrecisionMatrix(TpT0[1]`mat, 3) then
                                    sigma_vec := T[2] + T0[2];
                                    print "Sigma Equality to T+T0", sigma_vec;
                                else
                                    print "T-vector: ", T[2];
                                    error "Sigma No equality mod beta^2";
                                end if;
                            else
                                if ChangePrecisionMatrix(ChangeRing(psigma`negmat, Ram), 3) eq ChangePrecisionMatrix(T[1]`negmat, 3) then
                                    sigma_vec := T[2];
                                    print "Sigma Equality to T", sigma_vec;
                                elif ChangePrecisionMatrix(ChangeRing(psigma`negmat, Ram), 3) eq ChangePrecisionMatrix(TpT0[1]`negmat, 3) then
                                    sigma_vec := T[2] + T0[2];
                                    print "Sigma Equality to T+T0", sigma_vec;
                                else
                                    print "T-vector: ", T[2];
                                    error "Sigma No equality mod beta^2";
                                end if;
                            end if;
                        else
                            sigma_vec := T[2];
                            print "Sigma Distinguishable", sigma_vec;
                        end if;
                    end if;
                else
                    if ChangeRing(ChangeRing(tors_div_sigma`negmat, Ram), resmap) eq ChangeRing(T[1]`negmat, resmap) then
                        if T[2] in DoubleDivs then
                            psigma, sigma_list := find_mult(sigma_lst, p);

                            for L in LinComsRam do
                                if L[2] eq T[2] + T0[2] then
                                    TpT0 := L;
                                end if;
                            end for;

                            if assigned psigma`mat then
                                if ChangePrecisionMatrix(ChangeRing(psigma`mat, Ram), 3) eq ChangePrecisionMatrix(T[1]`mat, 3) then
                                    sigma_vec := T[2];
                                    print "Sigma Equality to T", sigma_vec;
                                elif ChangePrecisionMatrix(ChangeRing(psigma`mat, Ram), 3) eq ChangePrecisionMatrix(TpT0[1]`mat, 3) then
                                    sigma_vec := T[2] + T0[2];
                                    print "Sigma Equality to T+T0", sigma_vec;
                                else
                                    print "T-vector: ", T[2];
                                    error "Sigma No equality mod beta^3";
                                end if;
                            else
                                if ChangePrecisionMatrix(ChangeRing(psigma`negmat, Ram), 3) eq ChangePrecisionMatrix(T[1]`negmat, 3) then
                                    sigma_vec := T[2];
                                    S1 := T;
                                    print "Sigma Equality to T", sigma_vec;
                                elif ChangePrecisionMatrix(ChangeRing(psigma`negmat, Ram), 3) eq ChangePrecisionMatrix(TpT0[1]`negmat, 3) then
                                    sigma_vec := T[2] + T0[2];
                                    print "Sigma Equality to T+T0", sigma_vec;
                                else
                                    print "T-vector: ", T[2];
                                    error "Sigma No equality mod beta^3";
                                end if;
                            end if;
                        else
                            sigma_vec := T[2];
                            print "Sigma Distinguishable", sigma_vec;
                        end if;
                    end if;
                end if;
        
                if assigned tors_div_tau`mat then
                    if ChangeRing(ChangeRing(tors_div_tau`mat, Ram), resmap) eq ChangeRing(T[1]`mat, resmap) then
                        if T[2] in DoubleDivs then
                            ptau, tau_list := find_mult(tau_lst, p);

                            for L in LinComsRam do
                                if L[2] eq T[2] + T0[2] then
                                    TpT0 := L;
                                end if;
                            end for;

                            if assigned ptau`mat then
                                if ChangePrecisionMatrix(ChangeRing(ptau`mat, Ram), 3) eq ChangePrecisionMatrix(T[1]`mat, 3) then
                                    tau_vec := T[2];
                                    print "Tau Equality to T", tau_vec;
                                elif ChangePrecisionMatrix(ChangeRing(ptau`mat, Ram), 3) eq ChangePrecisionMatrix(TpT0[1]`mat, 3) then
                                    tau_vec := T[2] + T0[2];
                                    print "Tau Equality to T+T0", tau_vec;
                                else
                                    print "T-vector: ", T[2];
                                    error "Tau No equality mod beta^2";
                                end if;
                            else
                                if ChangePrecisionMatrix(ChangeRing(ptau`negmat, Ram), 3) eq ChangePrecisionMatrix(T[1]`negmat, 3) then
                                    tau_vec := T[2];
                                    print "Tau Equality to T", tau_vec;
                                elif ChangePrecisionMatrix(ChangeRing(ptau`negmat, Ram), 3) eq ChangePrecisionMatrix(TpT0[1]`negmat, 3) then
                                    tau_vec := T[2] + T0[2];
                                    print "Tau Equality to T+T0", tau_vec;
                                else
                                    print "T-vector: ", T[2];
                                    error "Tau No equality mod beta^2";
                                end if;
                            end if;
                        else
                            tau_vec := T[2];
                            print "Tau Distinguishable", tau_vec;
                        end if;
                    end if;

        
                else
                    if ChangeRing(ChangeRing(tors_div_tau`negmat, Ram), resmap) eq ChangeRing(T[1]`negmat, resmap) then
                        if T[2] in DoubleDivs then
                            ptau, tau_list := find_mult(tau_lst, p);

                            for L in LinComsRam do
                                if L[2] eq T[2] + T0[2] then
                                    TpT0 := L;
                                end if;
                            end for;

                            if assigned ptau`mat then
                                if ChangePrecisionMatrix(ChangeRing(ptau`mat, Ram), 3) eq ChangePrecisionMatrix(T[1]`mat, 3) then
                                    tau_vec := T[2];
                                    print "Tau Equality to T", tau_vec;
                                elif ChangePrecisionMatrix(ChangeRing(ptau`mat, Ram), 3) eq ChangePrecisionMatrix(TpT0[1]`mat, 3) then
                                    tau_vec := T[2] + T0[2];
                                    print "Tau Equality to T+T0", tau_vec;
                                else
                                    print "T-vector: ", T[2];
                                    error "Tau No equality mod beta^3";
                                end if;
                            else
                                if ChangePrecisionMatrix(ChangeRing(ptau`negmat, Ram), 3) eq ChangePrecisionMatrix(T[1]`negmat, 3) then
                                    tau_vec := T[2];
                                    print "Tau Equality to T", tau_vec;
                                elif ChangePrecisionMatrix(ChangeRing(ptau`negmat, Ram), 3) eq ChangePrecisionMatrix(TpT0[1]`negmat, 3) then
                                    tau_vec := T[2] + T0[2];
                                    print "Tau Equality to T+T0", tau_vec;
                                else
                                    print "T-vector: ", T[2];
                                    error "Tau No equality mod beta^3";
                                end if;
                            end if;
                        else
                            tau_vec := T[2];
                            print "Tau Distinguishable", tau_vec;
                        end if;
                    end if;
                end if;
            end for;
            return sigma_vec, tau_vec;
        end function;
        
        function LocalImageFromVecs(s_vec, t_vec)
            Qp_conv := Hp6!0;
            for i in [1..6] do
                if weil_pairing(tors_basis[i][2], s_vec) eq 0 then
                    if weil_pairing(tors_basis[i][2], t_vec) eq 0 then
                        Qp_conv := Qp_conv + embHp[i](QptoHp(1));
                    elif weil_pairing(tors_basis[i][2], t_vec) eq 1 then
                        Qp_conv := Qp_conv + embHp[i](QptoHp(p));
                    else
                        error "Weil pairing error";
                    end if;
                elif weil_pairing(tors_basis[i][2], s_vec) eq 1 then
                    if weil_pairing(tors_basis[i][2], t_vec) eq 0 then
                        Qp_conv := Qp_conv + embHp[i](QptoHp(a));
                    elif weil_pairing(tors_basis[i][2], t_vec) eq 1 then
                        Qp_conv := Qp_conv + embHp[i](QptoHp(p*a));
                    else
                        error "Weil pairing error";
                    end if;
                else
                    error "Weil pairing error";
                end if;
            end for;
            return Qp_conv;
        end function;
        
        function DivFromPoints(vP1, vP2, vP3)
            krnD1, krnD1piv := PseudoEchelonForm(Transpose(Matrix(Ram, [[Evaluate(m, P) : P in [vP1, vP2, vP3]] : m in monR[4]])));
            D1 := NewDiv(RightKernel(krnD1, krnD1piv));
            return D1;
        end function;
        
        return rec<DescentFunc | curve := C, singularity := Q, extension := extension, ord_divs := ord_divs, Hp := Hp, QptoHp := QptoHp, 
            Hp6 := Hp6, embHp := embHp, projHp := projHp, randpt := randompoint, randptQ := randomPointAboveQ, IsGalInv := IsGalInv, 
            IsSigmaAntiInv := IsSigmaAntiInv, IsTauAntiInv := IsTauAntiInv, IsAntiInv := IsAntiInv, IsZr := IsZr, find_mult := find_mult, 
            FindTwoTors := FindEqualTwoTorsion, LocalImageFromVecs := LocalImageFromVecs, DivFromPoints := DivFromPoints, TwoTorsion :=
            LinComsRam>;
        
    end if;
end function;
