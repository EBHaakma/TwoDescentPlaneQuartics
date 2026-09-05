intrinsic CrossProduct(a::SeqEnum,b::SeqEnum)->RngElt
  {naive cross product}
  return [a[2]*b[3]-a[3]*b[2],a[3]*b[1]-a[1]*b[3],a[1]*b[2]-a[2]*b[1]];
end intrinsic;

intrinsic InGeneralPosition(U::SeqEnum)-> .
{Determines if the three points [U[i],U[i+3]] for i=1,2,3 together
with the standard simplex are in general position (no three collinear,
no six on a conic)
}
    M:=Matrix([[1,0,0,1] cat U[1..3],
     [0,1,0,1] cat U[4..6],
     [0,0,1,1, 1, 1, 1]]);
    if exists{m: m in Minors(M,3)| m eq 0} then
        return false;
    end if;
    M:=Matrix([[1,0,0,0,0,0], [0,1,0,0,0,0],
        [0,0,1,0,0,0], [1,1,1,1,1,1]] cat
        [[u^2,v^2,1,u*v,u,v] where u:=U[i] where v:=U[i+3] : i in [1..3]]);
  return forall{m: m in Minors(M,6)| m ne 0};
end intrinsic;

idxij:=[[i,j]: j in [i+1..7], i in [1..6]];
Pu<uu1,uu2,uu3>:=ProjectiveSpace(Rationals(),2);
mon1:=MonomialsOfDegree(Parent(uu1),1);
mon3:=MonomialsOfDegree(Parent(uu1),3);
P2<X,Y,Z>:=ProjectiveSpace(Rationals(),2);

function make_integral(f)
    fm:=f/LeadingCoefficient(f);
    f_int:=LCM([Denominator(c): c in Coefficients(fm)])*fm;
    return f_int div GCD([Numerator(c): c in Coefficients(f_int)]);
end function;

function NormalizeForm(f)
    C:=Coefficients(f);
    return f div (GCD(C)*Sign(C[1]));
end function;

idxij:=[[i,j]: j in [i+1..7], i in [1..6]];

intrinsic ConstructSextic(U::SeqEnum) -> RngMPolElt
{Constructs the singular sextic with nodes at the given 7 points}
    pts:=[[1,0,0],[0,1,0],[0,0,1],[1,1,1],[U[1],U[4],1],[U[2],U[5],1],[U[3],U[6],1]];
    cubic_coeffs:=KernelMatrix(Transpose(Matrix(7,10,[Evaluate(m,p):m in mon3, p in pts])));
    PHI:=[make_integral(&+[c[i]*mon3[i]: i in [1..10]]):c in Rows(cubic_coeffs)];
    DPHI:=Matrix(3,3,[Derivative(PHI[i],j): i,j in [1..3]]); //this puts PHI[i] in a row

    //determine the cubics with a singularity at one of the base points
    lcs:=[KernelMatrix(Matrix(3,3,[Evaluate(g,Eltseq(p)): g in Eltseq(DPHI)]))[1]:p in pts];
    Li:=[make_integral(&+[l[i]*PHI[i]: i in [1..3]]): l in lcs];
    Lij:=[make_integral(&+[c[i]*mon1[i]: i in [1..3]]) where c:=CrossProduct(pts[I[1]],pts[I[2]]): I in idxij];
    Cu:=make_integral(Determinant(Matrix(3,3,[Derivative(PHI[i],j): i,j in [1..3]])));
    return Cu;
end intrinsic;

intrinsic ConstructQuartic(U::SeqEnum:MinRed:=true)-> RngMPolElt, SeqEnum
{Constructs the plane quartic given a sequence of six numbers describing
seven points in general position.
}
    pts:=[[1,0,0],[0,1,0],[0,0,1],[1,1,1],[U[1],U[4],1],[U[2],U[5],1],[U[3],U[6],1]];
    cubic_coeffs:=KernelMatrix(Transpose(Matrix(7,10,[Evaluate(m,p):m in mon3, p in pts])));
    PHI:=[make_integral(&+[c[i]*mon3[i]: i in [1..10]]):c in Rows(cubic_coeffs)];
    DPHI:=Matrix(3,3,[Derivative(PHI[i],j): i,j in [1..3]]); //this puts PHI[i] in a row

    //determine the cubics with a singularity at one of the base points
    lcs:=[KernelMatrix(Matrix(3,3,[Evaluate(g,Eltseq(p)): g in Eltseq(DPHI)]))[1]:p in pts];
    Li:=[make_integral(&+[l[i]*PHI[i]: i in [1..3]]): l in lcs];
    Lij:=[make_integral(&+[c[i]*mon1[i]: i in [1..3]]) where c:=CrossProduct(pts[I[1]],pts[I[2]]): I in idxij];
    Cu:=make_integral(Determinant(Matrix(3,3,[Derivative(PHI[i],j): i,j in [1..3]])));
    phi:=map<Pu->P2|PHI>;
    C:=make_integral(DefiningPolynomial(phi(Scheme(Pu,Cu))));
    ell:=[make_integral(DefiningPolynomial(phi(Scheme(Pu,g)))): g in Li cat Lij];
    if MinRed then
        Cm,Tm:=MinimizeReducePlaneQuartic(C);
    else
        Tm:=IdentityMatrix(Rationals(),3);
    end if;
    tr:=Eltseq(Vector([X,Y,Z])*ChangeRing(Transpose(Tm),Parent(X)));
    f:=make_integral(Evaluate(C,tr));
    ell:=[make_integral(Evaluate(g,tr)): g in ell];
    return f,ell;
end intrinsic;

Qt<t>:=PolynomialRing(Rationals());

intrinsic BitangentContactData(f::RngMPolElt,l::RngMPolElt) -> Tup
{returns a tuple <g(t), [x(t),y(t),z(t)]>
such that for g(t)=0, the contact points of the bitangent are parametrized.
if deg(g) != 2 then there is a contact point for t=\infty
if deg(g) = 0 or g has a double root, then l is a hyperflex.}
    K:=KernelMatrix(Matrix(3,1,[MonomialCoefficient(l,m): m in [X,Y,Z]] ));
    parm:=[K[1,i]+t*K[2,i]: i in [1..3]];
    fct:=Factorization(Evaluate(f,parm));
    assert forall{c: c in fct | IsEven(c[2])};
    g:=make_integral(&*[c[1]^(c[2] div 2): c in fct]);
    return <g,parm>;
end intrinsic;

bitang_labelling:=[{i,j}: j in [i+1..7], i in [0..6]];
S8:=Sym({0..7});
syz1:=Orbit(S8,{{0,1},{1,2},{2,3},{0,3}});
syz2:=Orbit(S8,{{0,1},{2,3},{4,5},{6,7}});
syzquads1:=[{Index(bitang_labelling,i): i in s}: s in syz1];
syzquads2:=[Setseq({Index(bitang_labelling,i): i in s}): s in syz2];
syzquads:=[Setseq(s): s in syzquads1 | #({1..7} meet s) ne 0] cat syzquads2;

intrinsic SyzQuads() -> SeqEnum
{returns the syzygetic quaduple indices on our bitangent ordering}
    return syzquads;
end intrinsic;

R<delta,c>:=PolynomialRing(Rationals(),8,"elim",[3,4,5,6,7,8]);
RR<XR,YR,ZR>:=PolynomialRing(R,3);
QRR:=&+[R.(i+2)*M[i]: i in [1..6]] where M:=MonomialsOfDegree(RR,2);
ZZ:=Integers();

intrinsic SyzQuadDelta(f::RngMPolElt,q::Any)->RngIntElt
{input: quartic f and a syzygetic quadruple of bitangent forms q
 output: a value delta such that delta* &*q is a square modulo f.}
    cfs:=Coefficients(Evaluate(&*q,[XR,YR,ZR])-delta*QRR^2+c*Evaluate(f,[XR,YR,ZR]));
    for i in [3..8] do
        J:=Ideal(cfs cat[R.i-1]);
        v:=Variety(J);
        if #v ne 0 then
            dval:=v[1][1];
            cval:=v[1][2];
            assert IsSquare((&*q +cval*f)/dval);
            return PowerFreePart(dval,2);
        end if;
    end for;
    error "does not appear to be a syzygetic quadruple";
end intrinsic;

intrinsic Discrim(F::RngMPolElt)-> .
{D_27, the discriminant of a quartic}
  R:=Parent(F);
  mons:=MonomialsOfDegree(R,5);
  x:=R.1;y:=R.2;z:=R.3;
  f:=[Derivative(F,i): i in [1..3]];
  J:=Determinant(Matrix([[Derivative(fi,j): j in [1..3]]:fi in f]));
  D:=[Derivative(J,i): i in [1..3]] cat [m*fi: m in [x^2,y^2,z^2,y*z,z*x,x*y], fi in f];
  return Determinant(Matrix([[MonomialCoefficient(d,m): m in mons]: d in D]))/2^17/3^9;
end intrinsic;

btrformat:=recformat<
    f: RngMPolElt,
    disc: RngIntElt,
    bitangs: SeqEnum,
    S: SeqEnum,
    H1S: ModTupFld,
    UsefulTriples: SeqEnum,
    ContactPoints: SeqEnum>;

intrinsic BitangRecord(U::SeqEnum:MinRed:=true)-> Rec
{}
    f,ell:=ConstructQuartic(U:MinRed:=MinRed);
    disc:=ZZ!Discrim(f);
    S:=[-1] cat PrimeDivisors(disc);
    Ds:=[SyzQuadDelta(f,ell[s]): s in syzquads];
    UsefulTriples:=[[]: i in [1..7]];
    for i in [1..210] do
        s:=syzquads[i];
        for j in [1..7] do
            if j in s then
                Append(~UsefulTriples[j],<Exclude(s,j),Ds[i]>);
            end if;
        end for;
    end for;
    
    R2<S2,T2>:=PolynomialRing(Integers(),2);
    ContactPoints:=[];
    for b in ell do
        kermat:=KernelMatrix(Matrix(3,1,[MonomialCoefficient(b,m):m in OrderedGenerators(Parent(b))]));
        kermat:=LCM([Denominator(a): a in Eltseq(kermat)])*kermat;
        U:=ChangeRing(kermat,R2);
        pt:=Eltseq(S2*U[1]+T2*U[2]);
        V:=Evaluate(f,pt);
        Append(~ContactPoints,<NormalizeForm(GCD([V,Derivative(V,1),Derivative(V,2)])),pt>);
    end for;
    H1S:=VectorSpace(GF(2),6*#S);
    return rec<btrformat|f:=f, disc:=disc, bitangs:=ell, S:=S, H1S:=H1S, UsefulTriples:=UsefulTriples, ContactPoints:=ContactPoints>;
end intrinsic;

intrinsic twoSelmerMap(Zp::RngPad)->.
{}
    F2:=GF(2);
    if Prime(Zp) eq 2 then
        dict:=[[F2|0,0],[],[1,0],[],[0,1],[],[1,1]];
        function modsq2(a)
            if RelativePrecision(a) le 2 then
                error "Insufficient precision";
            end if;
            v:=Valuation(a);
            return [F2|v mod 2] cat dict[(ZZ!ShiftValuation(a,-v)) mod 8];
        end function;
        return modsq2;
    else
        function modsqp(a)
            if RelativePrecision(a) eq 0 then
                error "Insufficient precision";
            end if;
            v:=Valuation(a);
            return [F2|v mod 2,IsSquare(ShiftValuation(a,-v)) select 0 else 1];
        end function;
        return modsqp;
    end if;
end intrinsic;
            
intrinsic PartialLocalImage(btr::Rec, p::RngIntElt, working_precision::RngIntElt) -> SetEnum, Map
{}
    f := btr`f;
    Zp := pAdicRing(p : Precision:=working_precision);
    Qp := FieldOfFractions(Zp);
    RQp:=PolynomialRing(Qp); sQp:=RQp.1;
    v4 := Valuation(Zp!4);
    Rp<xp,yp> := PolynomialRing(Zp, 2);
    Fp := ResidueClassField(Zp);
    A2k<xkp,ykp> := AffineSpace(Fp, 2);
    Pk:=[xkp,ykp];
    Rkp:=Parent(xkp);
    Bools:=Booleans();
    
    bitangents := btr`bitangs;
    UsefulTriples := btr`UsefulTriples;
    toSQp := twoSelmerMap(Zp);
    H1p := VectorSpace(GF(2), p eq 2 select 18 else 12);
    A := Matrix(GF(2), [toSQp(Zp!a) : a in btr`S]);
    H1StoH1p := hom< btr`H1S->H1p | DiagonalJoin([A,A,A,A,A,A]) >;

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
    
    Result:={};
    
    for P in ContactPoints do
        btP := [ Evaluate(b, P) : b in bitangents[1..7]];
        usable := [ RelativePrecision(a) gt v4 : a in btP ];
        if &and(usable) then
            w := [ toSQp(v) : v in btP ];
            Include(~Result, H1p!(&cat(w[1..6])) + H1p!(&cat[w[7],w[7],w[7],w[7],w[7],w[7]]) );
            continue; //we've found an image so we do NOT recurse on this point
        end if;
        btP2 := [ Evaluate(b, P) : b in bitangents[8..28] ];
        usable cat:= [ RelativePrecision(a) gt v4 : a in btP2 ];
        btP cat:= btP2;

        function select_value(U)
            if exists(u0){ u : u in U | &and(usable[u[1]]) } then
                return u0[2] * &*btP[u0[1]];
            else
                return 0;
            end if;
        end function;

        w := [];
        flag:=true;
        for i in [1..7] do
            if usable[i] then
                w[i]:=toSQp(btP[i]);
            else
                v:= select_value(UsefulTriples[i]);
                if v eq 0 then
                    flag:=false;
                    break;
                else
                    w[i]:=toSQp(v);
                end if;
            end if;
        end for;

        if flag then
            Include(~Result, H1p!(&cat(w[1..6])) + H1p!(&cat[w[7],w[7],w[7],w[7],w[7],w[7]]) );
            continue; 
        else
            error "Insufficient precision";
        end if;
    end for;
    r0:=Rep(Result);
    rk:=Rank(Matrix([r+r0: r in Result]));
    expected_rank:= (p eq 2) select 9 else 6;
    if rk gt expected_rank then
        error "span of local image to high-dimensional";
    end if;
    return Result, H1StoH1p, (rk eq expected_rank);
end intrinsic;
            
intrinsic LocalImage(btr::Rec, p::RngIntElt, working_precision::RngIntElt) -> SetEnum, Map
{}
    f := btr`f;
    Zp := pAdicRing(p : Precision:=working_precision);
    v4 := Valuation(Zp!4);
    Rp<xp,yp> := PolynomialRing(Zp, 2);
    Fp := ResidueClassField(Zp);
    A2k<xkp,ykp> := AffineSpace(Fp, 2);
    Pk:=[xkp,ykp];
    Rkp:=Parent(xkp);
    Bools:=Booleans();
    
    bitangents := btr`bitangs;
    UsefulTriples := btr`UsefulTriples;
    toSQp := twoSelmerMap(Zp);
    H1p := VectorSpace(GF(2), p eq 2 select 18 else 12);
    A := Matrix(GF(2), [toSQp(Zp!a) : a in btr`S]);
    H1StoH1p := hom< btr`H1S->H1p | DiagonalJoin([A,A,A,A,A,A]) >;

    Result:={};
    
    for Paff in [[xp,yp,1],[xp,1,p*yp],[1,p*xp,p*yp]] do
        fp := Evaluate(f, Paff);
        fp := fp div Content(fp);
        bitangents_affine := [Evaluate(b, Paff) :b in bitangents];
     
        procedure rec(fp, x0, y0, e, ~Result)
            fk := Evaluate(fp, Pk);
            gradfk := [ Derivative(fk, 1), Derivative(fk, 2) ];
            for P in RationalPoints(Scheme(A2k, fk)) do
                Ps := Eltseq(P);
                x1 := ZZ!Ps[1];
                y1 := ZZ!Ps[2];
                x0new := x0+p^e*x1;
                y0new := y0+p^e*y1;
                if exists{g : g in gradfk | Evaluate(g, Ps) ne 0} then
                    Paff := [Zp|elt<Zp | 0, x0new, e+1>, elt<Zp | 0, y0new, e+1>];
                    btP := [ Evaluate(b, Paff) : b in bitangents_affine[1..7]];
                    usable := [ RelativePrecision(a) gt v4 : a in btP ];
                    if &and(usable) then
                        w := [ toSQp(v) : v in btP ];
                        Include(~Result, H1p!(&cat(w[1..6])) + H1p!(&cat[w[7],w[7],w[7],w[7],w[7],w[7]]) );
                        continue; //we've found an image so we do NOT recurse on this point
                    end if;

                    btP2 := [ Evaluate(b, Paff) : b in bitangents_affine[8..28] ];
                    usable cat:= [ RelativePrecision(a) gt v4 : a in btP2 ];
                    btP cat:= btP2;

                    function select_value(U)
                        if exists(u0){ u : u in U | &and(usable[u[1]]) } then
                            return u0[2] * &*btP[u0[1]];
                        else
                            return 0;
                        end if;
                    end function;

                    w := [];
                    flag:=true;
                    for i in [1..7] do
                        if usable[i] then
                            w[i]:=toSQp(btP[i]);
                        else
                            v:= select_value(UsefulTriples[i]);
                            if v eq 0 then
                                flag:=false;
                                break;
                            else
                                w[i]:=toSQp(v);
                            end if;
                        end if;
                    end for;

                    if flag then
                        Include(~Result, H1p!(&cat(w[1..6])) + H1p!(&cat[w[7],w[7],w[7],w[7],w[7],w[7]]) );
                        continue; //we've found an image so we do NOT recurse on this point
                    else
                        print "We're lifting further!";
                    end if;
                end if;
                //at this point, either the point wasn't coming from a nonsingular
                //point in reduction or we didn't have enough precision to determine the value
                //of the bitangents. So we recurse on it.
                g := Evaluate(fp, [Rp|x1+p*xp, y1+p*yp]);
                rec(g div Content(g), x0new, y0new, e+1, ~Result);
           end for;
        end procedure;

        rec(fp, 0, 0, 0, ~Result);
    end for;

    return Result, H1StoH1p;
end intrinsic;

intrinsic RealLocalImage(btr::Rec, working_precision::RngIntElt)->.
{}
    Result:={};
    eps:=10^((-2*working_precision) div 3);
    RR:=RealField(working_precision);
    RRx<xRR>:=PolynomialRing(RR);
    ContactPoints:=[[Evaluate(v, [r[1],1]) : v in bt[2]]: r in Roots(Evaluate(bt[1],[xRR,1])), bt in btr`ContactPoints];
    ContactPoints:=[[v/m: v in C] where m:=Maximum([Abs(a): a in C]): C in ContactPoints];
    
    bitangents := btr`bitangs;
    UsefulTriples := btr`UsefulTriples;

    H1R:=VectorSpace(GF(2),6);
    for P in ContactPoints do
        btP := [ Evaluate(b, P) : b in bitangents[1..7]];
        usable := [ AbsoluteValue(a) gt eps : a in btP ];
        if &and(usable) then
            w := [ v gt 0 select 0 else 1 : v in btP ];
            Include(~Result, H1R!w[1..6] + H1R![w[7],w[7],w[7],w[7],w[7],w[7]]);
            continue; //we've found an image so we do NOT try other things.
        end if;
        btP2 := [ Evaluate(b, P) : b in bitangents[8..28] ];
        usable cat:= [ AbsoluteValue(a) gt eps : a in btP2 ];
        btP cat:= btP2;

        function select_value(U)
            if exists(u0){ u : u in U | &and(usable[u[1]]) } then
                return u0[2] * &*btP[u0[1]];
            else
                return 0;
            end if;
        end function;

        w := [];
        flag:=true;
        for i in [1..7] do
            if usable[i] then
                w[i]:=btP[i] gt 0 select 0 else 1;
            else
                v:= select_value(UsefulTriples[i]);
                if v eq 0 then
                    flag:=false;
                    break;
                else
                    w[i]:=v gt 0 select 0 else 1;
                end if;
            end if;
        end for;

        if flag then
            Include(~Result, H1R!w[1..6] + H1R![w[7],w[7],w[7],w[7],w[7],w[7]]);
            continue; 
        else
            error "Insufficient precision";
        end if;
    end for;

    assert #Result eq 4;
    A := Matrix(GF(2), [[Sign(a) eq 1 select 0 else 1] : a in btr`S]);
    H1StoH1R := hom< btr`H1S->H1R | DiagonalJoin([A,A,A,A,A,A]) >;
    return Result, H1StoH1R;
end intrinsic;
   
   //this routine is currently not used but is perhaps a little cleaner.
function lift(f,p)
    Fp:=GF(p);
    R<x,y>:=Parent(f);
    K:=BaseRing(R);
    A2p<xp,yp>:=AffineSpace(Fp,2);
    function work(f)
        Result:=[];
        fbar:=Evaluate(f,[xp,yp]);
        if Degree(fbar) eq 0 then
          return [];
        end if;
        dfx:=Derivative(f,1);
        dfy:=Derivative(f,2);
        pts:=RationalPoints(Curve(A2p,fbar));
        for pt in pts do
            ps:=Eltseq(pt);
            x0:=K!ps[1];
            y0:=K!ps[2];
            if Evaluate(dfx,ps) ne 0 or Evaluate(dfy,ps) ne 0 then
                Append(~Result, <K!ps[1],K!ps[2],1>);
            else
                g:=Evaluate(f,[x0+p*x,y0+p*y]);
                v:=Minimum([Valuation(c,p): c in Coefficients(g)]);
                Result cat:= [<x0+p*a[1],y0+p*a[2],a[3]+1>: a in work(g div p^v)];
            end if;
        end for;
        return Result;
    end function;
    function refine(x0,y0,e)
        g:=Evaluate(f,[x0+p^e*x,y0+p^e*y]);
        v:=Minimum([Valuation(c,p): c in Coefficients(g)]);
        g:=g div p^v;
        gbar:=Evaluate(g,[xp,yp]);
        pts:=RationalPoints(Curve(A2p,gbar));
        return [<x0+p^e*(K!pt[1]),y0+p^e*(K!pt[2]),e+1>: pt in pts];
    end function;
    return work(f), refine;
end function;   
