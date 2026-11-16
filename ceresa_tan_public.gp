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
	
	forsquarefree(d = -l, -1,
		D = d[1]*p;
		if(D % 4 == 2 || D % 4 == 3,
			order_dict = orders_in_single_field(D,l*p);
			if(order_dict != 0,
				listput(all_orders,[D,order_dict]);
			);
		);
	);
	forsquarefree(d = -4*l, 0,
		D = d[1]*p;
		if(D % 4 == 1,
			order_dict = orders_in_single_field(D, l*p);
			if(order_dict != 0,
				listput(all_orders,[D,order_dict]);
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
		counter += 1;
		listinsert(orders_update, [o[1], Map()], counter);
		foreach(o[2], item,
			if(l == 2,
				mapput(orders_update[counter][2], item[1][1], 2);
			);
			if(l != 2 && o[1] % l == 0,
				mapput(orders_update[counter][2], item[1][1], 2);
			);
			if(l != 2 && o[1] % l != 0,
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



\\initiate Eisenstein series
mf(k)=mfinit([1,k]);
E4(tau)=240*mfeval(mf(4),mfeisenstein(4),tau);
E6(tau)=-504*mfeval(mf(6),mfeisenstein(6),tau);



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
	pts_expected is the number m/2 from the article: the number of points on X_0(l*p) we are interested in above any curve with CM by fund_D*f^2
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

	\\a quadratic form for every element of the class group of the order 
	qfb_on_X01 = order_to_qfb(fund_D, f);
	
	m1 = 1/2;

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

			scaled_deriv_pt = djval_scaled(pt_lvllp) - 1/(l*p * pt_lvllp^2) * djval_scaled(-1 /(l*p* pt_lvllp)) + p/(l*p*pt_lvllp + y1*p)^2 * djval_scaled( (p*pt_lvllp - x1)/(l*p*pt_lvllp + p*y1) ) - l/(l*p*pt_lvllp + x1*l)^2 * djval_scaled( (l*pt_lvllp - y1)/(l*p*pt_lvllp + l*x1) );
			n = norm(scaled_deriv_pt);
			if(bitprecision(n) <= 2,
				print(concat(Str(p), "not enough precision"));
			);
			if(n <= tolerance,
				is_simple_zero = 0;
				listput(list_of_norms, n);
				return([is_unif, is_simple_zero, list_of_norms, fund_D, f]);
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
			\\print(item);
			L = check_order(l, p, fund_D, item[1][1], item[1][2], C, x1, y1, tolerance, norms);
			if(L[1] != 1 || L[2] != 1,
				fail_count += 1;
			);
			if(norms == 1, listput(list_of_all_norms, L[3]));
		);
	);

	return([fail_count, list_of_all_norms]);
}




/*
Example command:

forprime(p=1,200, if(setsearch(primes_to_exclude, p) == 0, print(check_tan_cond(2,p,0,10,0))));

*/