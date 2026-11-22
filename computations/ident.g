# Identification of Aut(O_Z) with G_2(2), and of the color groups K_Lambda with Delta(96) (Lambda = Z[i])
# and Sigma(72x3) (Lambda = Z[omega]).  Run after: python3 export_gap.py (writes autO.g, gauss.g, eis.g).
Read("autO.g"); Read("gauss.g"); Read("eis.g");
D := DerivedSubgroup(AutO);
Print("Aut(O_Z): order ", Size(AutO), "; derived subgroup of order ", Size(D), ", simple: ", IsSimple(D), ", ",
      IsomorphismTypeInfoFiniteSimpleGroup(D).name, "\n");
i := E(4); w := E(3); s := 1/(w - w^2);            # w - w^2 = sqrt(-3)
a := [[0,1,0],[0,0,1],[1,0,0]]; b := -[[0,0,1],[0,1,0],[1,0,0]];
c := DiagonalMat([i, i^-1, 1]); d := DiagonalMat([1, i, i^-1]);
D96 := Group([a, b, c, d]);                          # Escobar--Luhn generators, n = 4
C := DiagonalMat([1, w, w^2]); Em := [[0,1,0],[0,0,1],[1,0,0]];
V := s*[[1,1,1],[1,w,w^2],[1,w^2,w]]; Xm := s*[[1,1,w^2],[1,w,w],[w,1,w]];
S72 := Group([C, Em, V, Xm]);                        # Grimus--Ludl generators C, E, V, X
Sy := SylowSubgroup(S72, 3);
Print("Sigma(72x3): order ", Size(S72), ", ", StructureDescription(S72), "; Sylow 3-subgroup IdGroup ",
      IdGroup(Sy), " of exponent ", Exponent(Sy), ", normal: ", IsNormal(S72, Sy), "; quotient ",
      StructureDescription(S72/Sy), "\n");
Print("SU(3,2) = SU_3(F_2): order ", Size(SU(3,2)), ", IdGroup ", IdGroup(SU(3,2)), ", isomorphic to Sigma(72x3): ", IdGroup(SU(3,2)) = IdGroup(S72), "\n");
Report := function(K, G, name)
  local chi, A, act, orb, det1;
  chi := ClassFunction(G, List(ConjugacyClasses(G), cl -> TraceMat(Representative(cl))));
  A := AutomorphismGroup(G);
  act := function(x, alpha)
    return ClassFunction(G, List(ConjugacyClasses(G), cl -> (Representative(cl)^alpha)^x));
  end;
  orb := Orbit(A, chi, act);
  det1 := Filtered(Irr(G), x -> x[1] = 3 and Size(KernelOfCharacter(x)) = 1 and IsOne(DeterminantOfCharacter(x)));
  Print(name, ": standard group IdGroup ", IdGroup(G), ", K_Lambda IdGroup ", IdGroup(K),
        "; faithful irreducible degree-3 characters with determinant 1: ", Length(det1),
        ", all in the Aut-orbit of the natural character: ", ForAll(det1, x -> x in orb), "\n");
end;
Report(K_gauss, D96, "Delta(96), Lambda = Z[i]");
Report(K_eis, S72, "Sigma(72x3), Lambda = Z[omega]");
QUIT;
