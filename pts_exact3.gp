find_norm_soln(D,target) = 
{
	/*
	Find all solutions for the principal form of the maximal order of Q(sqrt(D)) represents target
	Pari already shows the solutions only up to units
	We expect D to be negative and squarefree
	target is l*p in our case
	see also https://ask.sagemath.org/question/76116/finding-all-integer-solutions-of-binary-quadratic-form/
	*/
	
	if( D % 4 == 1,
		return(qfbsolve(Qfb(1,1,(1-D)/4), target, 3));
	);
	return(qfbsolve(Qfb(1,0,-D), target, 3));
}



inlist(list, value)=for(i=1,#list, if(list[i]==value, return(i))); return(0);



orders_in_single_field(D, target) =
{
	/*
	Find all orders in the imaginary quadratic field Q(sqrt(D)) that have an element whose norm is target (i.e. l*p)
	Returns a dictionary where the keys are the conductors of these orders 
	and the value is the number of distinct principal ideals in this order whose norm is target
	The conductors can never be divisible by either p or l so we automatically have that the primes are invertible
	*/
	solns = find_norm_soln(D,target);	
	more_solns = List();	
	conductor_list = List();	
	if(length(solns) == 0,
		return(0);
	);

	\\when D == -1, only considering solutions up to units in the maximal order
	\\will not give all solutions up to units in suborders since the maximal order contains more units
	if(D == -1,
		foreach(solns, s,
			listput(more_solns,s);
			if(inlist(solns,[-1*s[2],s[1]]) == 0,
				listput(more_solns,[-1*s[2],s[1]]);
			);
		);
		foreach(more_solns, soln,
			b = soln[2];
			divs_except_1 = List(divisors(b));
			listpop(divs_except_1, 1);
			conductor_list = concat(conductor_list,divs_except_1);
		);
		conductor_w_mults = Map();
		for(i=1,matsize(matreduce(Vec(conductor_list)))[1],
			mapput(conductor_w_mults, matreduce(Vec(conductor_list))[i,1], matreduce(Vec(conductor_list))[i,2]);
		);
		mapput(conductor_w_mults, 1, length(solns));
	);

	\\same as for D == -1
	if(D == -3,\\same as the D=-1 case
		foreach(solns, s,
			listput(more_solns,s);
			if(inlist(solns,[-1*s[2],s[1] + s[2]]) == 0,
				listput(more_solns,[-1*s[2],s[1] + s[2]]);
			);
			if(inlist(solns,[-1*(s[1] + s[2]),s[1]]) == 0,
				listput(more_solns,[-1*(s[1] + s[2]),s[1]]);
			);
		);
		foreach(more_solns, soln,
			b = soln[2];
			divs_except_1 = List(divisors(b));
			listpop(divs_except_1, 1);
			conductor_list = concat(conductor_list,divs_except_1);
		);
		conductor_w_mults = Map();
		for(i=1,matsize(matreduce(Vec(conductor_list)))[1],
			mapput(conductor_w_mults, matreduce(Vec(conductor_list))[i,1], matreduce(Vec(conductor_list))[i,2]);
		);
		mapput(conductor_w_mults, 1, length(solns));
	);

	if(D != -1 && D !=-3,
		foreach(solns, soln,
			b = soln[2];
			conductor_list = concat(conductor_list,List(divisors(b)));
		);
		conductor_w_mults = Map();
		for(i=1,matsize(matreduce(Vec(conductor_list)))[1],
			mapput(conductor_w_mults, matreduce(Vec(conductor_list))[i,1], matreduce(Vec(conductor_list))[i,2]);
		);
	);
	return(conductor_w_mults);
}



all_norm_solutions(l,p) = 
{
	/*
	find all orders that contain a principal ideal of norm l*p
	returns a list of vectors, where the first entry is a negative squarefree integer D
	and the second entry is a dictionary where the keys are the conductors of the orders in Q(sqrt(D)) that contain a principal ideal of norm l*p
	and the value is the number of such ideals
	*/
	all_orders = List();
	
	forsquarefree(D = -l*p, -1,
		if(D[1] % 4 == 2 || D[1] % 4 == 3,
			order_dict = orders_in_single_field(D[1],l*p);
			if(order_dict != 0,
				listput(all_orders,[D[1],order_dict]);
			);
		);
	);
	forsquarefree(D = -4*l*p, 0,
		if(D[1] % 4 == 1,
			order_dict = orders_in_single_field(D[1], l*p);
			if(order_dict != 0,
				listput(all_orders,[D[1],order_dict]);
			);
		);
	);
	return(all_orders);
}



new_fix_pts(orders, l, p) = 
{
	/*
	Orders is list of vectors like the output of all_norm_solutions
    	For each dictionary, changes the value from the number of principal ideals of the order to the number of relevant points on X_0(l*p) per pair of points on X_0(p)
	(i.e. the number m from the thesis)
	*/
	
	orders_update = List();
	counter = 0;
	foreach(orders, o,
		leg = 1; \\Legendre symbol (o[1]|p) (at this point we are assuming that p>2)
		if(o[1] % p == 0,
			leg = 0;
		);
		counter += 1;
		listinsert(orders_update, [o[1], Map()], counter);
		foreach(o[2], item,
			if(item[1][2] == 1,
				mapput(orders_update[counter][2], item[1][1], 2);
			);
			if(item[1][2] == 2,
				mapput(orders_update[counter][2], item[1][1], 2*(2- leg));
			);
			if(item[1][2] == 4,
				mapput(orders_update[counter][2], item[1][1], 4);
			);
		);
	);
	
	return(orders_update);
}




\\----------------------------------------------------------------------------------------
\\----------------------------------------------------------------------------------------




\\Form the cartesian product of an unknown number of vectors

F(A,B)=[concat(a,b)| a<-A; b<-B];

cart_prod(L) = 
{
	return(fold(F,apply(S->[[s]|s<-S],L)));
}



order_to_qfb(fund_D, f) = 
{
	/*
	given an imaginary quadratic order, specified by fundamental discriminant fund_D and conductor f,
	compute all binary quadratic forms representing the different classes of the class group
	*/

	cl = quadclassunit(fund_D*f^2); \\gives cycle type of class group and generators

	list_of_forms = List();

	\\ the case of class number one, since PARI doesn't specify a generator here
	if(cl.no == 1,
		if(fund_D % 4 == 1,
			return(List([Qfb(1,f,f^2 * (1-fund_D)/4)])),
			return(List([Qfb(1,0,-f^2 * fund_D/4)]));
		);
	);

	\\compute all multiples of each generator as a list of lists
	for(c=1,length(cl.cyc),
		listput(list_of_forms, List());
		form = cl.gen[c];
		for(e=1,cl.cyc[c],
			listput(list_of_forms[c], form);
			form = qfbcomp(form,cl.gen[c]);
		);
	);

	\\transform list of lists to list of vectors
	list_of_vectors = List();
	for(c=1,length(list_of_forms),
		listput(list_of_vectors, Vec(list_of_forms[c]));
	);

	\\transform list of vectors to vector of vectors
	vector_of_vectors = Vec(list_of_vectors);

	\\construct the cartesian product to get representatives for all elements of class group
	vector_of_all_forms = cart_prod(vector_of_vectors);

	end_list = List();

	for(c=1,length(vector_of_all_forms),
		forms_to_mult = vector_of_all_forms[c];
		form = forms_to_mult[1];
		for(e=1,length(forms_to_mult),
			if(e < length(forms_to_mult), form = qfbcomp(form,forms_to_mult[e+1]));
		);
		listput(end_list, form);
	);

	return(end_list);
}


qfb_to_H_exact(Q,disc) = 
{
	\\take in a binary quadratic form Q of discriminant D and compute associated point in complex upper half plane (as a t_QUAD object)

	if(disc % 4 == 0,
		sqrt_D = 2*quadgen(disc),
		sqrt_D = 2*quadgen(disc) - 1
	);

	return((-1 * Vec(Q)[2] + sqrt_D )/(2*Vec(Q)[1]));
}



\\different order derivatives of j-invariant
/*
djval(tau) = derivnum(t=tau, ellj(t));
d2jval(tau) = derivnum(t=tau, ellj(t), 2);
d3jval(tau) = derivnum(t=tau, ellj(t), 3);
*/

\\different order derivatives of j + j w_p
/*
dunif(p,tau) = djval(tau) + p*djval(p*tau);
d2unif(p,tau) = d2jval(tau) + d2jval(p*tau)*p^2;
d3unif(p,tau) = d3jval(tau) + d3jval(p*tau)*p^3;
*/

\\x1,y1 such that x1*l + y1*p = 1
\\action of w_l is given by [l, -y; lp, lx]
\\action of w_p is given by [p, -x; lp, py]
\\different order derivatives of j w_l, j w_p, and j + j w_p - j w_l - j w_lp
/*
djvalwl(l,p,x1,y1,tau) = derivnum(t=tau, ellj( (l*t - y1)/(l*p*t + l*x1) ) );
d2jvalwl(l,p,x1,y1,tau) = derivnum(t=tau, ellj( (l*t - y1)/(l*p*t + l*x1) ), 2);
d3jvalwl(l,p,x1,y1,tau) = derivnum(t=tau, ellj( (l*t - y1)/(l*p*t + l*x1) ), 3);
djvalwp(l,p,x1,y1,tau) = derivnum(tau1=tau, ellj( (p*tau1 - x1)/(l*p*tau1 + p*y1) ) );
d2jvalwp(l,p,x1,y1,tau) = derivnum(t=tau, ellj( (p*t - x1)/(l*p*t + p*y1) ), 2);
d3jvalwp(l,p,x1,y1,tau) = derivnum(t=tau, ellj( (p*t - x1)/(l*p*t + p*y1) ), 3);
dfun(l,p,x1,y1,tau) = djval(tau) + djvalwp(l,p,x1,y1,tau) - djvalwl(l,p,x1,y1,tau) - l*p*djval(l*p*tau);
d2fun(l,p,x1,y1,tau) = d2jval(tau) + d2jvalwp(l,p,x1,y1,tau) - d2jvalwl(l,p,x1,y1,tau) - l^2 * p^2 * d2jval(l*p*tau);
d3fun(l,p,x1,y1,tau) = d3jval(tau) + d3jvalwp(l,p,x1,y1,tau) - d3jvalwl(l,p,x1,y1,tau) - l^3 * p^3 * d3jval(l*p*tau);
*/

\\initiate Eisenstein series
mf(k)=mfinit([1,k]);
E4(tau)=240*mfeval(mf(4),mfeisenstein(4),tau);
E6(tau)=-504*mfeval(mf(6),mfeisenstein(6),tau);


djval_scaled(tau) =
{
\\print(tau);
\\print(type(tau));
\\print(1.0*tau);
\\print(type(1.0*tau));
return(E6(1.0*tau)/E4(1.0*tau)*ellj(tau));
}


mat_act_qfb(M,Q) = 
{
	\\given some matrix (in  M_2(Z)) and a integral quadratic formm, lets the matrix act on the form

	return(Qfb( (Vec(Q)[1]) * (M[1,1])^2 + (Vec(Q)[3]) * (M[2,1])^2 + (Vec(Q)[2]) * (M[1,1]) * (M[2,1]),
	2 * ( (Vec(Q)[1]) * (M[1,1]) * (M[1,2]) + (Vec(Q)[3]) * (M[2,1]) * (M[2,2]) ) + (Vec(Q)[2]) * ( (M[1,1]) * (M[2,2]) + (M[1,2]) * (M[2,1]) ),
	(Vec(Q)[1]) * (M[1,2])^2 + (Vec(Q)[3]) * (M[2,2])^2 + (Vec(Q)[2]) * (M[1,2]) * (M[2,2]) ));
}



mat_inv(M) = 
{
	\\computes the adjugate of a matrix in M_2(Z)

	return([ M[2,2], -1 * M[1,2] ; -1 * M[2,1] , M[1,1] ]);
}



discr_qfb(Q) = 
{
	\\computes the discriminant of a quadratic form

	return( (Vec(Q)[2])^2 - 4* (Vec(Q)[1]) * (Vec(Q)[3]) );
}



prim_qfb(Q) = 
{
	\\divides out by the gcd of a quadratic form to make it primitive

	return( Qfb(Vec(Q)/gcd(Vec(Q))) );
}



qfb_on_X0lp_for_curve(l, p, fund_D, f, pts_expected, C, qfb_lvl1, w_p, w_l) =
{
	/*
	pts_expected is the number m*m' from thesis: the number of points on X_0(l*p) we are interested in above any curve with CM by fund_D*f^2
	C is a list/vector of representatives for Gamma0(l*p)\SL_2(Z)
	qfb_lvl1 is a quadratic form representing some curve with CM by fund_D*f^2
	w_p and w_l are matrices corresponding to the action of the respective Atkin-Lehner involutions
	finds all points on X_0(l*p) that we are interested in above the curve correponding to qfb_lvl1
	*/

	list_lvllp_qfb = List();
	point_count = 0;

	\\we let every representative of Gamma0(l*p)\SL_2(Z) act on the quadratic form qfb_lvl1 and find all points on X_0(l*p) that we are interested in
	foreach(C, M,
		qfb_lvllp = mat_act_qfb(mat_inv(M), qfb_lvl1);
		w_p_on_qfb = prim_qfb(mat_act_qfb(mat_inv(w_p), qfb_lvllp));
		if(discr_qfb(w_p_on_qfb) == fund_D * f^2,
			w_l_on_qfb = prim_qfb(mat_act_qfb(mat_inv(w_l), qfb_lvllp));
			if(discr_qfb(w_l_on_qfb) == fund_D* f^2,
				if(qfbred(w_p_on_qfb) == qfbred(w_l_on_qfb),
					point_count += 1;
					listput(list_lvllp_qfb, qfb_lvllp);
				);
			);
		);
		if(point_count == pts_expected, break);
	);

	if(pts_expected != point_count,
		error(concat(concat(Str(pts_expected - point_count), " point(s) missing on X_0(lp) for some quadratic form with fund_D*f^2 = "), fund_D * f^2));
	);
	
	return(list_lvllp_qfb);
}



check_order(l, p, fund_D, f, m, C, x1, y1, tolerance, norms) = 
{
	/*
	m (like in the thesis) is the number of relevant points on X_0(l*p) per pair of points on X_0(p)
	C is a list/vector of representatives for Gamma0(l*p)\SL_2(Z)
	x1 and y1 are integers such that x1*l + y1*p = 1
	tolerance is the lower bound on the norm for when we consider the derivatives to be nonzero
	set norms == 1 if you want to consider how close to vanishing these derivatives are
	checks if j + j w_p is a uniformizer and j + j w_p - j w_l - j w_lp has a simple zero at all relevant points
	*/
	
	\\print([fund_D, f]);

	\\a quadratic form for every element of the class group of the order 
	qfb_on_X01 = order_to_qfb(fund_D, f);
	
	if(fund_D % p == 0,
		m1 = 1/2,
		m1 = 1;
	);

	\\matrices for the Atkin-Lehner involutions
	w_p = [p, -1*x1; l*p, y1*p];
	w_l = [l, -1*y1; l*p, x1*l];

	is_unif = 1/2;
	is_simple_zero = 1/2;
	
	list_of_norms = List();

	\\do the check numerically on all relevant points on X_0(l*p)
	\\if we are considering elliptic points, we use the exact method described in the thesis
	foreach(qfb_on_X01, qfb_lvl1,
		list_of_qfb_lvllp = qfb_on_X0lp_for_curve(l, p, fund_D, f, m*m1, C, qfb_lvl1, w_p, w_l);
		foreach(list_of_qfb_lvllp, qfb_lvllp,
			pt_lvllp = qfb_to_H_exact(qfb_lvllp, fund_D*f^2);
			if(fund_D == -4 && f == 1,
				qfb_lvllp_red = qfbredsl2(qfb_lvllp);
				first_term = 1/(-1 * qfb_lvllp_red[2][2,1] * pt_lvllp + qfb_lvllp_red[2][1,1])^4;
				
				w_p_qfb_lvllp = prim_qfb(mat_act_qfb(mat_inv(w_p), qfb_lvllp));
				w_p_qfb_lvllp_red = qfbredsl2(w_p_qfb_lvllp);
				second_term = p^2/((l*p * pt_lvllp + y1*p)^4 * (-1 * w_p_qfb_lvllp_red[2][2,1] * qfb_to_H_exact(w_p_qfb_lvllp, fund_D*f^2) + w_p_qfb_lvllp_red[2][1,1])^4);
				
				w_l_qfb_lvllp = prim_qfb(mat_act_qfb(mat_inv(w_l), qfb_lvllp));
				w_l_qfb_lvllp_red = qfbredsl2(w_l_qfb_lvllp);
				third_term = l^2/((l*p * pt_lvllp + x1*l)^4 * (-1 * w_l_qfb_lvllp_red[2][2,1] * qfb_to_H_exact(w_l_qfb_lvllp, fund_D*f^2) + w_l_qfb_lvllp_red[2][1,1])^4);
				
				w_lp_qfb_lvllp = prim_qfb(mat_act_qfb(mat_inv([0,-1;l*p,0]), qfb_lvllp));
				w_lp_qfb_lvllp_red = qfbredsl2(w_lp_qfb_lvllp);
				fourth_term = 1/((l*p)^2 * pt_lvllp^4 * (-1 * w_l_qfb_lvllp_red[2][2,1] * qfb_to_H_exact(w_lp_qfb_lvllp, fund_D*f^2) + w_lp_qfb_lvllp_red[2][1,1])^4);
				
				scaled_second_deriv = first_term + second_term - third_term - fourth_term;
				if(scaled_second_deriv == 0, 
					is_simple_zero = 0;
					return([is_unif, is_simple_zero, list_of_norms, fund_D, f]);
				);
			);
			if(fund_D == -3 && f == 1,
				qfb_lvllp_red = qfbredsl2(qfb_lvllp);
				first_term = 1/(-1 * qfb_lvllp_red[2][2,1] * pt_lvllp + qfb_lvllp_red[2][1,1])^6;
				
				w_p_qfb_lvllp = prim_qfb(mat_act_qfb(mat_inv(w_p), qfb_lvllp));
				w_p_qfb_lvllp_red = qfbredsl2(w_p_qfb_lvllp);
				second_term = p^3/((l*p * pt_lvllp + y1*p)^6 * (-1 * w_p_qfb_lvllp_red[2][2,1] * qfb_to_H_exact(w_p_qfb_lvllp, fund_D*f^2) + w_p_qfb_lvllp_red[2][1,1])^6);
				
				w_l_qfb_lvllp = prim_qfb(mat_act_qfb(mat_inv(w_l), qfb_lvllp));
				w_l_qfb_lvllp_red = qfbredsl2(w_l_qfb_lvllp);
				third_term = l^3/((l*p * pt_lvllp + x1*l)^6 * (-1 * w_l_qfb_lvllp_red[2][2,1] * qfb_to_H_exact(w_l_qfb_lvllp, fund_D*f^2) + w_l_qfb_lvllp_red[2][1,1])^6);
				
				w_lp_qfb_lvllp = prim_qfb(mat_act_qfb(mat_inv([0,-1;l*p,0]), qfb_lvllp));
				w_lp_qfb_lvllp_red = qfbredsl2(w_lp_qfb_lvllp);
				fourth_term = 1/((l*p)^3 * pt_lvllp^6 * (-1 * w_l_qfb_lvllp_red[2][2,1] * qfb_to_H_exact(w_lp_qfb_lvllp, fund_D*f^2) + w_lp_qfb_lvllp_red[2][1,1])^6);
				
				scaled_third_deriv = first_term + second_term - third_term - fourth_term;
				if(scaled_second_deriv == 0, 
					is_simple_zero = 0;
					return([is_unif, is_simple_zero, list_of_norms, fund_D, f]);
				);
			);
			\\print(type((p*pt_lvllp - x1)/(l*p*pt_lvllp + p*y1)));
			\\print(type((l*t - y1)/(l*p*t + l*x1)));
			if((fund_D != -4 || f != 1 ) & (fund_D != -3 || f != 1),
				scaled_deriv_pt = djval_scaled(pt_lvllp) - 1/(l*p * pt_lvllp^2) * djval_scaled(-1 /(l*p* pt_lvllp)) + p/(l*p*pt_lvllp + y1*p)^2 * djval_scaled( (p*pt_lvllp - x1)/(l*p*pt_lvllp + p*y1) ) - l/(l*p*pt_lvllp + x1*l)^2 * djval_scaled( (l*pt_lvllp - y1)/(l*p*pt_lvllp + l*x1) );
				n = norm(scaled_deriv_pt);
				if(n <= tolerance & precision(n) >= 2,
					is_simple_zero = 0;
					listput(list_of_norms, n);
					return([is_unif, is_simple_zero, list_of_norms, fund_D, f]);
				);
			);
			if(norms == 1, listput(list_of_norms, n));
		);
	);
	
	is_unif = 1;
	is_simple_zero = 1;
	
	if(norms == 1, 
		listsort(list_of_norms);
		return([is_unif, is_simple_zero, list_of_norms]),
		return([is_unif, is_simple_zero]);
	);	
}




\\----------------------------------------------------------------------------------------
\\----------------------------------------------------------------------------------------




D_to_fund_D(D) = 
{
	\\returns the fundamental discriminant of the quadratic number field Q(sqrt(D)) with D squarefree

	if(D % 4 == 1, fund_D = D,
		fund_D = 4*D;
	);

	return(fund_D);
}


fund_D_to_D(fund_D) =
{
	\\returns D squarefree such that the fundamental discriminant of Q(sqrt(D)) is fund_D
	if(fund_D % 4 == 1, D = fund_D,
		D = fund_D/4;
	);
	
	return(D);
}



hilbert_poly(fund_D, f) =
{
	\\Hilbert class polynomial of order with discrimimant fund_D*f^2

	return(polclass(fund_D * f^2));
}



genus_X_0(p) =
{
	\\calculates the genus of X_0(p)
	
	k = p % 3;
	l = p % 4;
	v_3 = 0;
	v_2 = 0;
	if(k == 1,
		v_3 = 2;
	);
	if(k == 0,
		v_3 = 1;
	);
	if(l == 1,
		v_2 = 2;
	);
	if(l == 2,
		v_2 = 1;
	);
	return((p+1 - 3*v_2 - 4*v_3)/12);
}



genus_fricke_quot(p) =
{
	\\calculates the genus of the Fricke quotient X_0^+(p)

	g = genus_X_0(p);
	fix_pt_deg = qfbclassno(D_to_fund_D(-p));
	if(p == 2 || p == 3,
		return(0);
	);
	if(p % 4 == 3,
		fix_pt_deg += qfbclassno(D_to_fund_D(-p)*4);
	);
	return((g+1 - fix_pt_deg/2)/2);
}



T2_shadow_poly(p, orders) =
{
    	/*
	Calculate the function associated to a certain multiple n of the shadow of T_2 on X_0^+(p)
    	Which multiple depends on the class of p mod 12
    	Assumes p > 7
	if you use this function on its own, set orders = 0
	*/

	p12 = p % 12;
	p8 = p % 8;
	p7 = p % 7;
	p4 = p % 4;
	
	if(p12 == 11, n=2);
	if(p12 == 7, n=6);
	if(p12 == 5, n=4);
	if(p12 == 1, n=12);

	gplus = genus_fricke_quot(p);

	\\We will return a list of tuples, containing a polynomial mod p and an integer to which we should raise that polynomial,
	\\and a list of all the F_p-rational supersingular j-invariants (since PARI doesn't give us easy access to this and we will need them later)
	list_of_factors = List();
	
	/*
	We consider the fixed points which were already fixed points on X_0(p)
	(in the mean time we keep track of the degree of the total fixed point divisor)
	(we start with 4 since this is the degree we get from the cusp)
	*/
	
	deg_fix_pts = 4;

	if(setsearch([1,2,4], p7) != 0,
		listput(list_of_factors, [Mod(hilbert_poly(D_to_fund_D(-7), 1), p), n*(2*gplus - 2)*4]);
		deg_fix_pts += 4;
	);
	if(setsearch([1,3], p8) != 0,
		listput(list_of_factors, [Mod(hilbert_poly(D_to_fund_D(-2), 1), p), n*(2*gplus - 2)*2]);
		deg_fix_pts += 2;
	);
	if(p4 == 1,
		listput(list_of_factors, [Mod(hilbert_poly(D_to_fund_D(-1), 1), p), n*(2*gplus - 2)*2]);
		deg_fix_pts += 2;
	);
	
	\\Next the new fixed points
	if( orders != 0,
		new_fix_points = orders,
		new_fix_points = new_fix_pts(all_norm_solutions(2,p), 2, p);
	);
	
	foreach(new_fix_points, o,
		if(o[1] % p != 0,
			foreach(o[2], item,
				listput(list_of_factors, [Mod(hilbert_poly(D_to_fund_D(o[1]), item[1][1]), p), n*(2*gplus - 2)* item[1][2]]);
				deg_fix_pts += item[1][2];
			);
		);
		if(o[1] % p == 0,
			foreach(o[2], item,
				listput(list_of_factors, [Mod(hilbert_poly(D_to_fund_D(o[1]), item[1][1]), p), n*(2*gplus - 2)* item[1][2] / 2]);
				deg_fix_pts += item[1][2]/2;
			);
		);
	);

	\\Coefficient of the term 'n K_X' in the shadow of T_2
	deg_nK = 12 - deg_fix_pts;
	
	\\The fixed points from the Fricke involution
	fricke_fix_pts = List();
	listput(fricke_fix_pts, Mod(hilbert_poly(D_to_fund_D(-p), 1), p));
	if(p4 == 3,
		listput(fricke_fix_pts, Mod(hilbert_poly(D_to_fund_D(-p), 2), p));
	);
	
	\\F_p-rational supersingular j-invariants
	rat_ssj = List();
	foreach(fricke_fix_pts, poly,
		rat_ssj = concat(rat_ssj, List(polrootsmod(poly)));
	);
	rat_ssj = List(Set(rat_ssj));
	
	\\explicit description of the second modular polynomial
	modpoly2_modp = Mod(x^3 - x^2 * y^2 + 1488*x^2 * y - 162000*x^2 + 1488*x*y^2 + 40773375*x*y + 8748000000*x + y^3 - 162000*y^2 + 8748000000*y - 157464000000000, p);
	
	if(p12 == 11,
		\\The 'n K_X' part of shadow (we don't care about the coefficient of the cusp)
		foreach(fricke_fix_pts, f,
			listput(list_of_factors, [f, -1 * deg_nK]);
		);
		\\The '- 2 T_2(nK_X)' part of the shadow (again don't care about cusps)
		foreach(rat_ssj, j,
			listput(list_of_factors, [subst(modpoly2_modp, y, j), 8]);
		);
	);

	if(p12 == 7,
		\\The 'n K_X' part of shadow (we don't care about the coefficient of the cusp)
		foreach(fricke_fix_pts, f,
			listput(list_of_factors, [f, -3 * deg_nK]);
		);
		listput(list_of_factors, [Mod(x,p), -4 * deg_nK]);
		\\The '- 2 T_2(nK_X)' part of the shadow (again don't care about cusps)
		foreach(rat_ssj, j,
			listput(list_of_factors, [subst(modpoly2_modp, y, j), 24]);
		);
		listput(list_of_factors, [subst(modpoly2_modp, y, 0), 16]);
	);

	if(p12 == 5,
		\\The 'n K_X' part of shadow (we don't care about the coefficient of the cusp)
		foreach(fricke_fix_pts, f,
			listput(list_of_factors, [f, -2 * deg_nK]);
		);
		listput(list_of_factors, [Mod(x-1728,p), -2 * deg_nK]);
		\\The '- 2 T_2(nK_X)' part of the shadow (again don't care about cusps)
		foreach(rat_ssj, j,
			listput(list_of_factors, [subst(modpoly2_modp, y, j), 16]);
		);
		listput(list_of_factors, [subst(modpoly2_modp, y, 1728), 8]);
	);
	
	if(p12 == 1,
		\\The 'n K_X' part of shadow (we don't care about the coefficient of the cusp)
		foreach(fricke_fix_pts, f,
			listput(list_of_factors, [f, -6 * deg_nK]);
		);
		listput(list_of_factors, [Mod(x,p), -8 * deg_nK]);
		listput(list_of_factors, [Mod(x-1728,p), -6 * deg_nK]);
		\\The '- 2 T_2(nK_X)' part of the shadow (again don't care about cusps)
		foreach(rat_ssj, j,
			listput(list_of_factors, [subst(modpoly2_modp, y, j), 48]);
		);
		listput(list_of_factors, [subst(modpoly2_modp, y, 0), 32]);
		listput(list_of_factors, [subst(modpoly2_modp, y, 1728), 24]);
	);
	
	return([list_of_factors, rat_ssj]);
}



eval_shadow_poly(list_of_factors, ssj) = 
{
	/*
	list_of_factors is part of output of T2_shadow_poly(p)
	ssj is a supersingular j-invariant which is not in F_p
	evaluates the function f_2 on ssj by multiplying the values of all nonzero factors and keeps track of if there are any factors that vanish at ssj
	*/

	product = 1;
	zero_exp = 0;
	
	foreach(list_of_factors, f,
		val = subst(f[1], x, ssj);
		if(val != 0,
			product *= val^f[2],
			zero_exp += f[2];
		);
	);
	return([product, zero_exp]);
}




T2_shadow_check(p, stop_on_success, max_trials, show_trials, orders) =
{
	/*
	PARI only allows us to request a random j-invariant over F_p, so we need to keep repeating this until we find one that works
	Set stop_on_success to either 1 or 0, corresponding to whether you want to stop as soon as find a j-invariant that works
	or keep trying until you have either found all possible j-invariants or hit the maximum max_trials
	Set max_trials to the max trials you want to do and -1 if you want to continue until all non-rational ssj have been tried
	Set show_trials to either 1 or 0, depending on if you want to see how far along the program is
	If you use this function on its own, set orders = 0
	*/
	
	if(orders != 0,
		[poly, rat_ssj] = T2_shadow_poly(p, orders),
		[poly, rat_ssj] = T2_shadow_poly(p);
	);

	\\find the number of supersingular j that are not F_p rational
	eps1728= 0;
	if(p % 4 == 3, eps1728 = 1);
	eps0 = 0;
	if(p % 3 == 2, eps0 = 1);
	total_ssj = (p - (p % 12))/12 + eps1728 + eps0;
	number_nonrat_ssj = total_ssj - length(rat_ssj);

	nonrat_ssj = Set();
	
	trial_count = 0;
	new_ssj_trial_count = 0;
	zero_exp_count = 0;
	nonzero_rat_count = 0;
	success_count = 0;
	
	\\keep trying supersingular j until we hit one of our stop conditions
	while(trial_count != max_trials,
		trial_count += 1;
		if(show_trials && max_trials != -1,
			if(trial_count % floor(max_trials/10) == 0, print(trial_count));
		);
		j = ellsupersingularj(p);
		if(ffmap(fffrobenius(j,1), j) != j && !setsearch(nonrat_ssj, j),
			new_ssj_trial_count += 1;
			nonrat_ssj = setunion(nonrat_ssj, Set(j));
			[product, zero_exp] = eval_shadow_poly(poly, j);
			if(zero_exp > 0,
				zero_exp_count += 1;
			);
			frob_prod = ffmap(fffrobenius(product,1), product);
			if(zero_exp == 0 && frob_prod == product,
				nonzero_rat_count += 1;
			);
			if(zero_exp == 0 && frob_prod != product,
				success_count += 1;
				if(stop_on_success == 1,
					return([p, "Success", trial_count, new_ssj_trial_count, number_nonrat_ssj, zero_exp_count, nonzero_rat_count, success_count]);
				);
			);
			if(new_ssj_trial_count == number_nonrat_ssj,
				if(success_count > 0,
					return([p, "Success", trial_count, new_ssj_trial_count, number_nonrat_ssj, zero_exp_count, nonzero_rat_count, success_count]),
					return([p, "No counterexample", trial_count, new_ssj_trial_count, number_nonrat_ssj, zero_exp_count, nonzero_rat_count, success_count]);
				);
			);
		);
		
	);
	if( success_count > 0,
		return([p, "Success", trial_count, new_ssj_trial_count, number_nonrat_ssj, zero_exp_count, nonzero_rat_count, success_count]),
		return([p, "No counterexample", trial_count, new_ssj_trial_count, number_nonrat_ssj, zero_exp_count, nonzero_rat_count, success_count]);
	);

}



\\those primes p where X_0^+(p) has genus less than 3
primes_to_exclude = Set([2,3,5,7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,101,103,107,131,167,191]);




\\----------------------------------------------------------------------------------------
\\----------------------------------------------------------------------------------------




\\define the matrix group PSL_2(Z)
PSL2 = [[0,1;-1,0], [1,1;0,1]];



check_tan_cond(l,p,orders,tolerance, norms) = 
{
	/*
	Checks if the function if the correct derivative of j + j w_p - j w_l - j w_lp does not vanish on X_0(l*p) and records the number of fails
	tolerance is the lower bound on the norm for when we consider the derivatives to be nonzero
	If you use this function on its own, set orders = 0
	Set norms to either 0 or 1, depending on if you actually want to see how big these norms are e.g. to see how the precision influences the result
	*/
	
	\\coset representatives of Gamma_0(l*p)\SL_2(Z)
	[C, N] = mscosets(PSL2, g->g[2,1] % (l*p) == 0);

	\\x1, y1 such that x1*l + y1*p = 1
	[x1,y1] = bezout(l,p);

	fail_count = 0;
	list_of_all_norms =List();
	
	if(orders != 0,
		order_list = orders,
		order_list = new_fix_pts(all_norm_solutions(l,p),l,p);
	);
	
	foreach(order_list, field,
		fund_D = D_to_fund_D(field[1]);
		foreach(field[2], item,
			L = check_order(l, p, fund_D, item[1][1], item[1][2], C, x1, y1, tolerance, norms);
			if(L[1] != 1 || L[2] != 1,
				fail_count += 1;
			);
			if(norms == 1, listput(list_of_all_norms, L[3]));
		);
	);

	return([fail_count, list_of_all_norms]);
}



check_Ceresa_T2_shadow(p, check_tan, tolerance) =
{
	/*
	Checks if the reduction of the shadow of T_2 is trivial or not
	Set check_tan to 1 or 0, depending on if you also want to verify the condition on j + j w_p - j w_l - j w_lp
	tolerance is the same as in check_tan_cond
	*/

	orders = new_fix_pts(all_norm_solutions(2,p), 2, p);
	if(check_tan == 1,
		fail_count = check_tan_cond(2,p,orders, tolerance, 0)[1];
		if(fail_count > 0,
			return(concat("condition on tangent failed: ", Str(fail_count)));
		);
		return(["satisfies condition on tangent", T2_shadow_check(p,1,-1,0, orders)]);
	);
	return(T2_shadow_check(p,1,-1,0, orders));
}



/*
Example command:

forprime(p=1,200, if(setsearch(primes_to_exclude, p) == 0, print(check_Ceresa_T2_shadow(p, 1, 10))));

*/
