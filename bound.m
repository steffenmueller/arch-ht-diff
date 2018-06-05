
/*************************************************************************************************
* Upper bound on the archimedean part of the local decomposition of the difference between the   *
* naive and the canonical height on an elliptic curve over a number field.                       *
*                                                                                                *
* This uses representation theory of the two-torsion subgroup, similar to earlier work of        *
* Stoll for Jacobians of genus 2 and hyperelliptic genus 3 curves, and a refinement (also        *
* due to Stoll) already used by Müller-Stoll for genus 2 and by Stoll for genus 3.               *
*                                                                                                *
*                             C. Stumpe & J.S. Müller, 2018                                      *
*                                                                                                * 
**************************************************************************************************/




function stoll_bound_ith_embedding( E, i : eps := 10^-3, prec := 30, geometric := false ) 
  // E is an elliptic curve over a number field K.
  // Compute the upper bound between the archimedean part of the local decomposition of the
  // difference between the naive and canonical height on E, embedded into the complex numbers 
  // using the ith embedding of K into the complex numbers (ordering given by Magma's Conjugates).
  // The iteration in the refinement of the bound stops when the difference between successive 
  // bounds is less than eps. 
  // prec is the precision used in the computations.
  // If geometric is true, then the upper bound is valid over the complex numbers even if 
  // the embedding is real.

  vprintf Height, 1 : "Starting computation for embedding %o.\n", i;
  r,s := Signature(BaseRing(E));                    
  if i gt r then i := 2*i-r-1; end if; // Find the correct embedding according to Magma's ordering
  b2,b4,b6 := Explode([ Conjugate(b, i ) : b in bInvariants(E) ]);
  rts := Roots(Polynomial(ComplexField(prec), [ b6/4, b4/2, b2/4, 1 ])); 
  assert #rts eq 3;  // If this fails, increase prec.
  r1 := rts[1][1];  r2 := rts[2][1];  r3 := rts[3][1]; // x-coordinates of the two-torsion points

  a_matrix := ZeroMatrix(RealField(prec), 2, 3);
  b_matrix := ZeroMatrix(ComplexField(prec), 3, 2);

  // Let (x1,x2) represent the image of a point on E under the map to P^1 induced by
  // projection onto the x-coordinate.
  // Then one can write the squares of x1, x2 as linear combinations of certain 
  // quadratic forms y_j(x1,x2) with coefficients a_ij.
  a_matrix[1,1] := Abs((2*r2*r3-b4/2)/(2*(r1-r2)*(r1-r3)));
  a_matrix[1,2] := Abs((2*r1*r3-b4/2)/(2*(r2-r1)*(r2-r3)));
  a_matrix[1,3] := Abs((2*r1*r2-b4/2)/(2*(r3-r1)*(r3-r2)));
  a_matrix[2,1] := Abs(-1/(2*(r1-r2)*(r1-r3)));
  a_matrix[2,2] := Abs(-1/(2*(r2-r1)*(r2-r3)));
  a_matrix[2,3] := Abs(-1/(2*(r3-r1)*(r3-r2)));
  vprintf Height, 3 : "a_matrix = \n%o.\n", a_matrix;

  // The squares of the y_i(x1,x2) can be written as linear combinations of the quartic
  // duplication polynomials delta_j(x1,x2) with coefficients b_ij.
  b_matrix[1,1] := 1;  b_matrix[1,2] := -r1;
  b_matrix[2,1] := 1;  b_matrix[2,2] := -r2;
  b_matrix[3,1] := 1;  b_matrix[3,2] := -r3;
  vprintf Height, 3 : "b_matrix = \n%o.\n", b_matrix;

  phi := function( ds );
    // This is used to iteratively refine the upper bound.
    d1,d2 := Explode(ds);
    assert d1 ge 0 and d2 ge 0;

    if i gt r or geometric then // complex embedding, 
                                // or real embedding, but we're interested in a geometric bound.
      y_bound := [ Sqrt(Abs(b_matrix[i,1])*d1 + Abs(b_matrix[i,2])*d2) : i in [1..3] ]; 

    else        // real embedding. Use that the delta_j(x) are real, but the b_ij might not be.
      y_bound := [ Sqrt(Max(Abs(b_matrix[i,1]*d1 + b_matrix[i,2]*d2), 
                            Abs(b_matrix[i,1]*d1 - b_matrix[i,2]*d2))) : i in [1..3] ];
    end if;

    return [ Sqrt(&+[ a_matrix[1,j]*y_bound[j] : j in [1..3] ]),  
                  Sqrt(&+[ a_matrix[2,j]*y_bound[j] : j in [1..3] ]) ]; 
  end function;

  vn := phi([ RealField(prec) | 1,1 ]);
  vprintf Height, 3 : "phi(1,1) = %o.\n", vn;
  bound := (4/3)*Log(Maximum([ Abs(v) : v in vn ]));  // First bound, obtained from a bound on
                                                      // Phi via the geometric series.
  vprintf Height, 1 : "Unrefined bound = %o.\n", bound;
  n := 1; 
  repeat  // Do at least one iteration.
    old_bound := bound;
    assert old_bound le bound;  // The quality of the bound should not decrease.
    vn := phi(vn); // Perform the iteration step.
    vprintf Height, 3 : "phi^%o(1,1) = %o.\n", n+1, vn;
    n +:=  1;
    bound := (4^n)/(4^n -1) * Log(Maximum([ Abs(v) : v in vn ]));
    vprintf Height, 2 : "New bound = %o.\n", bound;
  until old_bound - bound lt eps; // Stop when sufficiently close to limit.
  vprintf Height, 2 : "Used %o iterations for refinement.\n", n-1;
  vprintf Height, 1 : "Refined bound = %o.\n", bound;
  return bound;
end function;


intrinsic StollBound( E::CrvEll : Epsilon := 10^-3, Precision := 30, Geometric := false ) 
              -> FldReElt 
{If E is an elliptic curve over a number field, this computes an upper bound for 
  the archimedean contribution to the difference between the naive and the canonical 
  height. The bound is computed using the representation theory of the two-torsion 
  subgroup of E, suitably refined using a contracting function. The iteration stops
  when the difference between successive bounds is less than the optional parameter 
  Epsilon. If Geometric is set, then we compute a bound valid for complex points.}
  

  K := BaseField(E);
  require K cmpeq Rationals() or ISA(Type(K), FldNum):
          "The curve must be defined over the rationals or a number field.";

  if ISA(Type(K), FldNum) then 
    require IsAbsoluteField(K): 
          "The curve must be defined over an absolute extension of the rationals.";
  end if;
  r,s := Signature(K); 
  // Take into account that complex conjugate embeddings give the same contribution
  weights := [ 1: i in [1..r] ] cat [ 2: i in [r+1..r+s] ]; 

  // Compute the upper bound for all archimedean places
  bound_list := [ stoll_bound_ith_embedding(E, i: eps := Epsilon, 
                              prec := Precision, geometric := Geometric) : i in [1..r+s] ];

  return RealField() ! &+[ weights[i] * bound_list[i] : i in [1..r+s] ] / Degree(K);
end intrinsic;
