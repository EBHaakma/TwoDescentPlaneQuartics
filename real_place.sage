//input the defining polynomial of C and the ordered list of its bitangents
//the output is the local image at p = -1

def RealPlace(f, bitangs):
    X = f.parent().0
    Y = f.parent().1
    Z = f.parent().2
    C = Curve(f)
    S1 = C.riemann_surface(prec=100)
    P = S1.period_matrix()

    from riemann_theta.riemann_theta import RiemannTheta
    Omega1=P[:,:3]
    Omega2=P[:,3:]
    Omega1i=(Omega1)^(-1)
    Omega=Omega1i*Omega2

    RT=RiemannTheta(Omega)
    odd=[v for v in GF(2)^6 if v[:3]*v[3:] == 1]
    values=[vector(RT(char=c,derivs=[[0],[1],[2]]))*Omega1i for c in odd]
    bt=[v/max(v,key=lambda a: abs(a)) for v in values]
    def reconstruct(a):
        p=algdep(a,1)
        return -p[0]/p[1]

    VecF2 = VectorSpace(GF(2), 6)

    new_labels = list(zip([VecF2([o[0], o[1], o[2], o[5], o[4], o[3]]) for o in odd],[[reconstruct(c) for c in b] for b in bt]))
    new_labels

    BitangentLabeling = [
    vector(GF(2), [ 0, 0, 1, 1, 0, 0 ]),
    vector(GF(2), [ 1, 0, 1, 1, 0, 0 ]),
    vector(GF(2), [ 1, 0, 0, 0, 1, 1 ]),
    vector(GF(2), [ 1, 1, 0, 0, 0, 1 ]),
    vector(GF(2), [ 1, 0, 1, 0, 0, 1 ]),
    vector(GF(2), [ 1, 0, 0, 1, 0, 1 ]),
    vector(GF(2), [ 0, 0, 1, 1, 0, 1 ]),
    vector(GF(2), [ 0, 1, 0, 0, 1, 1 ]),
    vector(GF(2), [ 0, 1, 1, 1, 0, 0 ]),
    vector(GF(2), [ 0, 0, 1, 1, 1, 0 ]),
    vector(GF(2), [ 0, 1, 0, 1, 1, 0 ]),
    vector(GF(2), [ 0, 1, 1, 0, 1, 0 ]),
    vector(GF(2), [ 1, 1, 0, 0, 1, 0 ]),
    vector(GF(2), [ 1, 1, 1, 1, 0, 0 ]),
    vector(GF(2), [ 1, 0, 1, 1, 1, 0 ]),
    vector(GF(2), [ 1, 1, 0, 1, 1, 0 ]),
    vector(GF(2), [ 1, 1, 1, 0, 1, 0 ]),
    vector(GF(2), [ 0, 1, 0, 0, 1, 0 ]),
    vector(GF(2), [ 1, 0, 0, 0, 0, 1 ]),
    vector(GF(2), [ 1, 1, 1, 0, 0, 1 ]),
    vector(GF(2), [ 1, 1, 0, 1, 0, 1 ]),
    vector(GF(2), [ 0, 1, 1, 1, 0, 1 ]),
    vector(GF(2), [ 1, 0, 1, 0, 1, 1 ]),
    vector(GF(2), [ 1, 0, 0, 1, 1, 1 ]),
    vector(GF(2), [ 0, 0, 1, 1, 1, 1 ]),
    vector(GF(2), [ 1, 1, 1, 1, 1, 1 ]),
    vector(GF(2), [ 0, 1, 0, 1, 1, 1 ]),
    vector(GF(2), [ 0, 1, 1, 0, 1, 1 ])
    ]

    def force_pos_x(l):
        cand = l
        if cand[0] < 0:
            cand = [-1*c for c in cand]
        return cand

    #represent the bitangents in the same way that sage reconstructs them
    def coefficient_vector(f):
        max_abs = max(abs(f.monomial_coefficient(X)), abs(f.monomial_coefficient(Y)), abs(f.monomial_coefficient(Z)))
        if max_abs == abs(f.monomial_coefficient(X)):
            max_val = f.monomial_coefficient(X)
        elif max_abs == abs(f.monomial_coefficient(Y)):
            max_val = f.monomial_coefficient(Y)
        else:
            max_val = f.monomial_coefficient(Z)
        return force_pos_x(list([f.monomial_coefficient(Z)/max_val, f.monomial_coefficient(Y)/max_val, f.monomial_coefficient(X)/max_val]))

    bitang_vectors = [coefficient_vector(b) for b in bitangs]
    bitang_vectors

    old_labels = list(zip(BitangentLabeling, bitang_vectors))
    old_labels

    old_labels_sort = sorted(old_labels, key=lambda tup: tup[1])

    new_labels_1 = [n[0] for n in new_labels];
    new_labels_2_posx = [force_pos_x(n[1]) for n in new_labels]
    new_labels_posx = list(zip(new_labels_1, new_labels_2_posx))
    new_labels_sort = sorted(new_labels_posx, key=lambda tup: tup[1])

    V_new = list([v[0] for v in new_labels_sort])
    W_old = list([w[0] for w in old_labels_sort])

    list([v[1] for v in new_labels_sort]) == list([w[1] for w in old_labels_sort])

    new_labels_sort

    old_labels_sort

    V_vec = [VecF2(v) for v in V_new]
    W_vec = [VecF2(w) for w in W_old]
    V_vec = [v-V_vec[0] for v in V_vec]
    W_vec = [w-W_vec[0] for w in W_vec]

    equations = []
    rhs = []

    for v, w in zip(V_vec, W_vec):
        for i in range(6):
            row = [0]*36
            for j in range(6):
                row[6*i + j] = v[j]
            equations.append(row)
            rhs.append(w[i])

    M = Matrix(GF(2), equations)
    b = vector(GF(2), rhs)

    solution = M.solve_right(b)
    A = Matrix(GF(2), 6, 6, solution)

    G = identity_matrix(GF(2), 6)
    G = G[::-1]
    A.T*G*A

    B = [v/2 for v in P.T]

    def imm(v):
        v.set_immutable()
        return v

    V = [imm(v) for v in GF(2)^6]

    D = dict( (v,sum(a*b for a,b in zip(v.lift(),B))) for v in V )
    W = [S1.reduce_over_period_lattice((D[v]/2)+(D[v]/2).conjugate()) for v in V]

    four_tors = [min(V, key = lambda v:S1.reduce_over_period_lattice(D[v]+w).norm()) for w in W]
    four_tors = [VecF2([v[3], v[4], v[5], v[2], v[1], v[0]]) for v in four_tors]
    four_tors

    new_labels_four_tors = [A*v for v in four_tors]
    new_labels_four_tors

    def weil_pairing(A, B):
        return A[0]*B[5]+A[1]*B[4]+A[2]*B[3]+A[3]*B[2]+A[4]*B[1]+A[5]*B[0]

    tors_basis = [BitangentLabeling[i] - BitangentLabeling[0] for i in [1..6]]
    tors_basis

    def LocalImageFromVec(v):
        return vector(GF(2), [weil_pairing(v, T) for T in tors_basis])

    basis = span([LocalImageFromVec(v) for v in new_labels_four_tors]).basis()
    output = [list(b) for b in basis]
    return output
