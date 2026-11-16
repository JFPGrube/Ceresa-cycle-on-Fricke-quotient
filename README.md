# Ceresa-cycle-on-Fricke-quotient
Program to verify that the Ceresa cycle of X_0^+(p), the quotient of the modular curve X_0(p) by the Fricke involution, is not torsion up to rational equivalence. In the article ... it is explained how this works.

The file ceresa_tan_public.gp provides an implementation in PARI/GP of Algorithm 4.12 of this article. An example command for how this may be used can be found at the very end of the file.

The file ceresa_public.ipynb is an implementation in SageMath which can be used to verify that the Ceresa cycle of X_0^+(p) is not torsion up to rational equivalence. The correctness of this implementation is dependent on the result of ceresa_tan_public (as explained in the article.
