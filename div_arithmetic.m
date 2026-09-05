ArithFunc := recformat< f : RngMPolElt, p : Integers(), P, Pmat, ext, mul, pull, sum, neg, Zr, IsZr, IsGalInv, IsSigmaAntiInv, IsTauAntiInv, IsAntiInv>;
Div := recformat<mat, negmat>;

function strip(M)
    return Matrix([r: r in Rows(M)| exists{a: a in Eltseq(r) | RelativePrecision(a) gt 0}]);
end function;

function PseudoEchelonForm(B)
    Nrows := NumberOfRows(B);
    Ncols := NumberOfColumns(B);
    R := BaseRing(B);
    F := FieldOfFractions(R);
    pi := UniformizingElement(F);
    newB := B;
    pivot_cols := [];
    for i := 1 to Nrows do
        if exists{j: j in [1..Ncols] | RelativePrecision(newB[i,j]) gt 0} then
            min := Valuation(newB[i,1]); //our pivot is where the valuation is minimal
            pos := [i, 1];
            for a := 1 to Ncols do
                for b := i to Nrows do
                    val := Valuation(newB[b,a]);
                    if val lt min then
                        min := val;
                        pos := [b, a];
                    end if;
                    if min eq 0 then
                        break a;
                    end if;
                end for;
            end for;
            if (min gt 0) and (not newB[pos[1],pos[2]] eq 0) then //if Valuation is non-zero, divide lower rows by p
                sub := Submatrix(newB, i, 1, Nrows - i + 1, Ncols);
                matQp := ChangeRing(sub, F);
                matQp := pi^(-min)*matQp;
                sub := ChangeRing(matQp, R);
                InsertBlock(~newB, sub, i, 1);
                print "Precision loss", min;
            end if;
            SwapRows(~newB, i, pos[1]); //swap the pivot to the correct row
            MultiplyRow(~newB, 1 div newB[i, pos[2]], i);
            Append(~pivot_cols, pos[2]); //add to the list of pivot columns
            for j := 1 to Nrows do
                if not j eq i then
                    AddRow(~newB, -(newB[j][pos[2]] div newB[i][pos[2]]), i, j);
                end if;
            end for;
        end if;
    end for;
    return strip(newB), pivot_cols;
end function;

function RightKernel(B, pivots)
    R:=BaseRing(B);
    n:=Ncols(B);
    V:=RSpace(R,n);
    assert #pivots eq Nrows(B);
    pivset:=Seqset(pivots);
    freeloc:=Setseq({1..n} diff pivset);
    L:=[];
    for j in [1..#freeloc] do
        v:=V!0;
        v[freeloc[j]]:=1;
        for i in [Nrows(B) .. 1 by -1] do
            c:=InnerProduct(B[i],v);
            if RelativePrecision(c) gt 0 then
                piv:=pivots[i];
                assert RelativePrecision(B[i,piv]-1) eq 0;
                v[piv]:=-c;
            end if;
        end for;
        Append(~L,v);
    end for;
    return PseudoEchelonForm(Matrix(L));
end function;

function NewDiv(M : negmat:=0)
    if negmat eq 0 then
        return rec<Div | mat := M>;
    else
        return rec<Div | mat := M, negmat := negmat>;
    end if;
end function;

function InitArithFunc(f, p, R, P, dmax, offset)
    k:=BaseRing(Parent(f));
    L<X,Y,Z>:=PolynomialRing(Integers(),3);
    P2<X,Y,Z>:=Proj(L);
    C:=Curve(P2,f);
    mon:=[MonomialsOfDegree(L,d): d in [1..dmax]];
    dim:=[#m:m in mon];
    Zp := pAdicRing(p, 50);
    Qp := pAdicField(p, 50);
    Unram<alpha> := BaseRing(R);
    PUnram<x> := PolynomialRing(Unram);
    RamF := FieldOfFractions(R);
    
    function tau(z)
        z := R!z;
        coeff := Coefficients(z);
        newCoeff := [coeff[1], -coeff[2]];
        return ChangePrecision(R!newCoeff, AbsolutePrecision(z));
    end function;

    alpha_imag := Trace(alpha) - alpha;

    function sigma(z)
        z := R!z;
        coeffBeta := Coefficients(z);
        coeffReal := Coefficients(coeffBeta[1]);
        coeffImag := Coefficients(coeffBeta[2]);
        newCoeff := [coeffReal[1] + coeffReal[2]*alpha_imag, coeffImag[1] + coeffImag[2]*alpha_imag];
        return ChangePrecision(R!newCoeff, AbsolutePrecision(z));;
    end function;
    
    function construct_W(d)
        W:=RModule(Integers(),#mon[d]);
        tovec:=func<f| W![MonomialCoefficient(f,m):m in mon[d]]>;
        topol:=func<v| &+[v[i]*mon[d][i]: i in [1..#mon[d]]]>;
        return W, tovec,topol;
    end function;

    Wd:=[];
    tovecd:=[];
    topold:=[];
    for d in [1..dmax] do
        Wd[d],tovecd[d],topold[d]:=construct_W(d);
    end for;

    function construct_mucoeff(n,m)
        return [[tovecd[n+m](topold[n](a)*topold[m](b)) : b in Basis(Wd[m])] : a in Basis(Wd[n])];
    end function;
    
    function construct_mu(n,m,R)
        mucoeff:=construct_mucoeff(n,m);
        mucoeff:=[[ChangeRing(a,R): a in b]:b in mucoeff];
        U := Universe(mucoeff[1]);
        r := Rank(U);
        B := BaseRing(U);
        V := VectorSpace(FieldOfFractions(B), r);
        mu:=func<v,w | &+[V | ChangeRing(mucoeff[i][j], FieldOfFractions(R))*v[i]*w[j] : i in [1..dim[n]], j in [1..dim[m]] | v[i] ne 0 and w[j] ne 0]>;
        return mu;
    end function;

    function construct_muB(n,m,R)
        mucoeff:=construct_mucoeff(n,m);
        mucoeff:=[[ChangeRing(a,R): a in b]:b in mucoeff];
        U := Universe(mucoeff[1]);
        r := Rank(U);
        B := BaseRing(U);
        V := VectorSpace(FieldOfFractions(B), r);
        mu:=func<v,j | &+[V | ChangeRing(mucoeff[i][j], FieldOfFractions(R))*v[i] : i in [1..dim[n]] | v[i] ne 0]>;
        return mu;
    end function;

    function construct_muBB(n,m,R)
        mucoeff:=construct_mucoeff(n,m);
        mucoeff:=[[ChangeRing(a,R): a in b]:b in mucoeff];
        mu:=func<i,j | ChangeRing(mucoeff[i][j], FieldOfFractions(R))>;
        return mu;
    end function;

    Wd:=[ChangeRing(W,R): W in Wd];
    munm:=[[construct_mu(n,m,R) : m in [1..dmax-n]]: n in [1..dmax]];
    muBnm:=[[construct_muB(n,m,R) : m in [1..dmax-n]]: n in [1..dmax]];
    muBBnm:=[[construct_muBB(n,m,R) : m in [1..dmax-n]]: n in [1..dmax]];
    
    function convert(V)
        con := [RamF!v : v in Eltseq(V)];
        return con;
    end function;

    function oldmul(A,B)
        n:=Index(dim,Ncols(A));
        m:=Index(dim,Ncols(B));
        return Matrix([(convert(munm[n][m](a,b))): a in Rows(A), b in Rows(B)]);
    end function;

    fvec:=convert(tovecd[4](L!f));
    fmat:=[* i lt 4 select [] else i eq 4 select Matrix([fvec]) else
            PseudoEchelonForm(oldmul(Matrix([fvec]),Matrix(Basis(Wd[i-4])))): i in [1..8]*];
            
    function mul(A,B:target:=0)
        A:=ChangeRing(A, RamF);
        B:=ChangeRing(B, RamF);
        n:=Index(dim,Ncols(A));
        m:=Index(dim,Ncols(B));
        R:=RamF;
        p:=Integers()!UniformizingElement(BaseRing(R));
        if target eq 0 then
            codimA:=Ncols(A)-Nrows(A);
            codimB:=Ncols(B)-Nrows(B);
            target:=dim[n+m]-codimA-codimB;
        end if;
        if Nrows(A) eq 1 or Nrows(B) eq 1 or target ge Nrows(A)*Nrows(B) then
            return PseudoEchelonForm(Matrix([(munm[n][m](a,b)): a in Rows(A), b in Rows(B)]));
        end if;
        if fmat[n+m] cmpne [] then
            newmat:=fmat[n+m];
        else
            newmat:=Matrix(R, 1, dim[n+m], [0: i in [1..dim[n+m]]]);
        end if;
        RowsA := Rows(A);
        RowsB := Rows(B);
        repeat
            RandomCoeffA := [Random([0..p-1]) : i in [1..#RowsA]];
            LinComA := &+[RandomCoeffA[i]*RowsA[i] : i in [1..#RowsA]];
            RandomCoeffB := [Random([0..p-1]) : i in [1..#RowsB]];
            LinComB := &+[RandomCoeffB[i]*RowsB[i] : i in [1..#RowsB]];
            image := munm[n][m](LinComA, LinComB);
            newmat := VerticalJoin(newmat, Matrix(image));
            if Nrows(newmat) ge target+offset then
                cand, candpivs := PseudoEchelonForm(newmat);
                if Nrows(cand) eq target then
                    return cand, candpivs;
                    break;
                elif Nrows(cand) lt target then
                    print "Have not met target", target, Nrows(cand);
                else
                    error "Overshot target", target, Nrows(cand);
                    break;
                end if;
            end if;
        until false;
        return PseudoEchelonForm(newmat);
    end function;
    
    function pull(A,pivots,n:target:=0)
        m:=Index(dim,Ncols(A));
        R:=BaseRing(A);
        codimA := Ncols(A)-Nrows(A);
        if target eq 0 then
            target := dim[n]-codimA;
        end if;
        krn:=Transpose(RightKernel(A, pivots));
        BasisWn:=Basis(Wd[n]);
        BasisWd:=Basis(Wd[m-n]);
        newmat:=Matrix(R, #BasisWn, 1, [0: i in [1..#BasisWn]]); //initialize a matrix
        for j in [1..#BasisWd] do
            U:=Matrix([muBBnm[n][m-n](i,j)*krn : i in [1..#BasisWn]]);
            newmat:=HorizontalJoin(newmat, U);
            if Ncols(newmat) ge codimA+offset then
                B, Bpivs := PseudoEchelonForm(Transpose(newmat));
                cand, candpivs := RightKernel(B, Bpivs);
                if Nrows(cand) eq target then
                    return cand, candpivs;
                    break j;
                else
                    print "Have not met target", target, Nrows(cand);
                end if;
            end if;
        end for;
    end function;
    
    if Type(Parent(P[1])) eq FldRat then
        lcm:=LCM([Denominator(c) : c in Eltseq(P)]);
        v:=[c*lcm : c in Eltseq(P)];
        v:=[L!elt : elt in v];
        assert Evaluate(f,v) eq 0;
        IP:=[v[2]*X-v[1]*Y,v[3]*X-v[1]*Z,v[2]*Z-v[3]*Y];
        MP_1, MP_1pivs:=PseudoEchelonForm(Matrix([convert(tovecd[1](g)): g in IP]));
    else
        v := [Qp!elt : elt in P];
        PolyQpRng<XQp, YQp, ZQp> := PolynomialRing(Qp, 3);
        fQp := PolyQpRng!ChangeRing(f, Qp);
        test := Evaluate(fQp, v);
        assert test eq BigO(Qp!p^Minimum(AbsolutePrecision(test), 50));
        IP := [v[2]*XQp - v[1]*YQp, v[3]*XQp - v[1]*ZQp, v[2]*ZQp - v[3]*YQp];
        Wp := RModule(Qp, #MonomialsOfDegree(PolyQpRng, 1));
        veclst := [Wp![MonomialCoefficient(g, m) : m in MonomialsOfDegree(PolyQpRng, 1)] : g in IP];
        MP_1, MP_1pivs := PseudoEchelonForm(Matrix(veclst));
    end if;
    MP_2, MP_2pivs:=mul(MP_1,Matrix(Basis(Wd[1])));
    M2P_4, M2P_4pivs:=mul(MP_2,MP_2);
    M4P_8, M4P_8pivs:=mul(M2P_4,M2P_4);
    M4P_4, M4P_4pivs:=pull(M4P_8,M4P_8pivs,4);
    M8P_8, M8P_8pivs:=mul(M4P_4,M4P_4);
    M8P_6, M8P_6pivs:=pull(M8P_8,M8P_8pivs,6);
    M9P_8, M9P_8pivs:=mul(M8P_6,MP_2);
    M9P_4, M9P_4pivs:=pull(M9P_8,M9P_8pivs,4);
    
    bvec:=pull(M9P_4, M9P_4pivs, 3);
    bvec:=Matrix([bvec[Nrows(bvec)]]);
    bvec_8, bvec_8pivs:=PseudoEchelonForm(VerticalJoin(mul(bvec,Matrix(Basis(Wd[5]))),fmat[8]));
    krn:=Transpose(RightKernel(bvec_8, bvec_8pivs));
    BasisW4 := Basis(Wd[4]);
    mat_init:=Matrix(RamF, #BasisW4, 1, [0: i in [1..#BasisW4]]);
    for w in Rows(M9P_4) do
        U := Matrix([muBnm[4][4](w,j)*krn : j in [1..#BasisW4]]);
        mat_init:=HorizontalJoin(mat_init, U);
        if Ncols(mat_init) ge 3+offset then
            B, Bpivs := PseudoEchelonForm(Transpose(mat_init));
            MDp_4, MDp_4pivs := RightKernel(B, Bpivs);
            if Nrows(MDp_4) eq 12 then
                break w;
            end if;
        end if;
    end for;
    
    function AddFlip(D1, D2)
        MD1D2_8, MD1D2_8pivs:=mul(D1,D2);
        MD1D2_4:=pull(MD1D2_8,MD1D2_8pivs,4);
        MD1D2Dp_8, MD1D2Dp_8pivs:=mul(MD1D2_4,MDp_4);
        MD1D2Dp_4, MD1D2Dp_4pivs:=pull(MD1D2Dp_8,MD1D2Dp_8pivs,4);
    
        gvec:=pull(MD1D2Dp_4, MD1D2Dp_4pivs, 3);
        gvec:=Matrix([gvec[Nrows(gvec)]]);
        gvec_8, gvec_8pivs:=PseudoEchelonForm(VerticalJoin(mul(gvec,Matrix(Basis(Wd[5]))),fmat[8]));
        krn:=Transpose(RightKernel(gvec_8, gvec_8pivs));
    
        BasisW4 := Basis(Wd[4]);
        mat_init:=Matrix(RamF, #BasisW4, 1, [0: i in [1..#BasisW4]]);
        for w in Rows(MD1D2Dp_4) do
            U := Matrix([muBnm[4][4](w,j)*krn : j in [1..#BasisW4]]);
            mat_init:=HorizontalJoin(mat_init, U);
            if Ncols(mat_init) ge 3+offset then
                B, Bpivs := PseudoEchelonForm(Transpose(mat_init));
                MD3, MD3pivs := RightKernel(B, Bpivs);
                if Nrows(MD3) eq 12 then
                    break w;
                end if;
            end if;
        end for;
        return MD3;
    end function;
    
    M3P_6, M3P_6pivs := PseudoEchelonForm(VerticalJoin(mul(M2P_4,MP_2),fmat[6]));
    Zrmat, Zrpivs := pull(M3P_6, M3P_6pivs, 4);
    Zr := NewDiv(Zrmat);
    Zr`negmat := Zrmat;
    
    function divneg(D1)
        D := rec<Div |>;
        if assigned D1`mat then
            D`negmat := D1`mat;
        end if;
        if assigned D1`negmat then
            D`mat := D1`negmat;
        end if;
        return D;
    end function;
    
    function divsum(D1, D2)
        if assigned D1`mat and assigned D2`mat then
            return rec<Div | negmat := AddFlip(D1`mat, D2`mat)>, D1, D2;
        elif assigned D1`negmat and assigned D2`negmat then
            return rec<Div | mat := AddFlip(D1`negmat, D2`negmat)>, D1, D2;
        elif assigned D1`mat and assigned D2`negmat then
            D1`negmat := AddFlip(D1`mat, Zrmat);
            return rec<Div | mat := AddFlip(D1`negmat, D2`negmat)>, D1, D2;
        elif assigned D1`negmat and assigned D2`mat then
            D2`negmat := AddFlip(D2`mat, Zrmat);
            return rec<Div | mat := AddFlip(D1`negmat, D2`negmat)>, D1, D2;
        else
            error "No matrix assigned";
        end if;
    end function;

    resR<ar>, resmap := ResidueClassField(R);
    ZrZp:=ChangeRing(Zrmat, R);
    ZrReduced:=EchelonForm(ChangeRing(ZrZp,resmap));
    function IsEqualToZr(D)
        if assigned D`mat then
            L := D`mat;
        elif assigned D`negmat then
            L := D`negmat;
        else
            error "No matrix assigned";
        end if;
        LReduced := EchelonForm(ChangeRing(ChangeRing(L, R),resmap));
        return LReduced eq ZrReduced;
    end function;
    
    function IsMatrixGaloisInvariant(D)
        if assigned D`mat then
            M := D`mat;
        else
            M := D`negmat;
        end if;
        M_conjneg_sigma := AddFlip(Matrix(R, Nrows(M), Ncols(M), [sigma(m) : m in Eltseq(M)]), Zrmat);
        M_conjneg_tau := AddFlip(Matrix(R, Nrows(M), Ncols(M), [tau(m) : m in Eltseq(M)]), Zrmat);
        M_sum_sigma := NewDiv(AddFlip(M, M_conjneg_sigma));
        M_sum_tau := NewDiv(AddFlip(M, M_conjneg_tau));
        return IsEqualToZr(M_sum_sigma) and IsEqualToZr(M_sum_tau);
    end function;
    
    function IsMatrixSigmaAntiInvariant(D)
        if assigned D`mat then
            M := D`mat;
        else
            M := D`negmat;
        end if;
        M_conj_sigma := Matrix(R, Nrows(M), Ncols(M), [sigma(m) : m in Eltseq(M)]);
        M_conjneg_tau := AddFlip(Matrix(R, Nrows(M), Ncols(M), [tau(m) : m in Eltseq(M)]), Zrmat);
        M_sum_sigma := NewDiv(AddFlip(M, M_conj_sigma));
        M_sum_tau := NewDiv(AddFlip(M, M_conjneg_tau));
        return IsEqualToZr(M_sum_sigma) and IsEqualToZr(M_sum_tau);
    end function;
    
    function IsMatrixTauAntiInvariant(D)
        if assigned D`mat then
            M := D`mat;
        else
            M := D`negmat;
        end if;
        M_conjneg_sigma := AddFlip(Matrix(R, Nrows(M), Ncols(M), [sigma(m) : m in Eltseq(M)]), Zrmat);
        M_conj_tau := PseudoEchelonForm(Matrix(R, Nrows(M), Ncols(M), [tau(m) : m in Eltseq(M)]));
        M_sum_sigma := NewDiv(AddFlip(M, M_conjneg_sigma));
        M_sum_tau := NewDiv(AddFlip(M, M_conj_tau));
        return IsEqualToZr(M_sum_sigma) and IsEqualToZr(M_sum_tau);
    end function;
    
    function IsMatrixGaloisAntiInvariant(D)
        if assigned D`mat then
            M := D`mat;
        else
            M := D`negmat;
        end if;
        M_conj_sigma := PseudoEchelonForm(Matrix(R, Nrows(M), Ncols(M), [sigma(m) : m in Eltseq(M)]));
        M_conj_tau := PseudoEchelonForm(Matrix(R, Nrows(M), Ncols(M), [tau(m) : m in Eltseq(M)]));
        M_sum_sigma := NewDiv(AddFlip(M, M_conj_sigma));
        M_sum_tau := NewDiv(AddFlip(M, M_conj_tau));
        return IsEqualToZr(M_sum_sigma) and IsEqualToZr(M_sum_tau);
    end function;
    
    return rec<ArithFunc | f := f, p := p, P := P, Pmat := MP_1, ext := R, mul := mul, pull := pull, 
              sum := divsum, neg := divneg, Zr := Zr, IsZr := IsEqualToZr, IsGalInv := IsMatrixGaloisInvariant, 
              IsSigmaAntiInv := IsMatrixSigmaAntiInvariant, IsTauAntiInv := IsMatrixTauAntiInvariant, 
              IsAntiInv := IsMatrixGaloisAntiInvariant>;
end function;

