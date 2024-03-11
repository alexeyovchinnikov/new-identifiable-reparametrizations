
restart:


#The coefff and DecomposePolynomial are taken from 
# https://github.com/pogudingleb/AllIdentifiableFunctions
coefff:=proc(P, t)
    local L, H, i, k:
    L:=[coeffs(P, indets(P), 'h_aux_for_coef')]: H:=[h_aux_for_coef]: k:=0:
    for i from 1 to nops(H) do
        if H[i]=t then k:=L[i] fi:
    end do:
    return k;
end proc:


DecomposePolynomial := proc(p, vars_main, vars_coef, infolevel)
    # Input: p - polynomial in two groups of variables: vars_main and vars_coef
    # Computes a decomposition of minimal length of p as a linear combination 
    # of products A * B, where A is a polynomial in vars_main and B 
    # is a polynomial in vars_coef return two lists: list of A's and list of B's
    local cf, monoms, result_cf, result_monom, i, c, m, j, lc, lm, coeff_in_c:
    cf := [coeffs(collect(p, vars_main, 'distributed'), vars_main, 'monoms')]:
    monoms := [monoms]:
    result_cf := []:
    result_monom := Array([]):
    if infolevel > 0 then
        printf("        Number of monomials: %a\n", nops(cf)):
    end:
    for i from 1 to nops(cf) do
        c := cf[i]:
        m := monoms[i]:
        for j from 1 to nops(result_cf) do
            lc, lm := Groebner[LeadingTerm](result_cf[j], plex(op(vars_coef))):
            coeff_in_c := coefff(c, lm):
            c := c - coeff_in_c / lc * result_cf[j]:
            result_monom[j] := result_monom[j] + coeff_in_c / lc * m:
        end do:
        if c <> 0 then
            result_cf := [op(result_cf), c]:
            ArrayTools[Append](result_monom, m):
        end if:
    end do:
    if infolevel > 0 then
        printf("        Reduced to: %a\n", nops(result_cf)):
    end:
    return [result_cf, convert(result_monom, list)]:
end proc:

printf("\n================================================\n");
printf("= Software demo for the Biohydrogenation example =\n");
printf("================================================\n\n");

# Loading packages
with(DifferentialAlgebra):
with(DifferentialAlgebra[Tools]):


with(ListTools):
with(ArrayTools):
with(VectorCalculus):
with(LinearAlgebra):

with(PolynomialIdeals):


#setting up the system
sys_rhs := [
            - k5 * x4(t) / (k6 + x4(t)),
            k5 * x4(t) / (k6 + x4(t)) - k7 * x5(t)/(k8 + x5(t) + x6(t)),
            k7 * x5(t) / (k8 + x5(t) + x6(t)) - k9 * x6(t) * (k10 - x6(t)) / k10,
            k9 * x6(t) * (k10 - x6(t)) / k10
    ]:   
params := [k5, k6, k7, k8, k9, k10]:
states := [x4, x5, x6, x7]:
outputs := [y1, y2]:
output_func := [x4(t), x5(t)]:
inputs := []:
syst := [
         seq(diff(states[i](t),t) - sys_rhs[i], i = 1..numelems(states)), 
         seq(outputs[i](t) - output_func[i], i = 1..numelems(outputs))
        ]:
printf("==================\n");
printf("The ODE system is:\n\n");

no_t_states := [seq(states[i](t) = states[i], i = 1..numelems(states))]:
for i from 1 to numelems(states) do printf("%a' = %a\n", states[i],  subs(no_t_states, sys_rhs[i])) od;
for i from 1 to numelems(outputs) do printf("%a\n", outputs[i] = subs(no_t_states, output_func[i])) od;
# Computing input-output equations
R := DifferentialRing(
                      blocks = [states, outputs, inputs], 
                      derivations = [t], 
                      arbitrary = params
                     ):

RG := RosenfeldGroebner(syst, R)[1]:
eq := Equations(RG):
IOeqs := simplify(eq[-numelems(outputs)..-1]):
printf("\n===================\n");
printf("The IO-equations are:\n\n %a = 0\n\n", IOeqs);
# Replacing derivatives with regular variables for further computation

Rout := DifferentialRing(
                      blocks = [outputs,inputs], 
                      derivations = [t], 
                      arbitrary = params
                     ):
LD := LeadingDerivative(IOeqs, Rout):
outputs_maxorders := [seq([FactorDerivative(v, R)], v in LD)]:
Rin := DifferentialRing(
                      blocks = [inputs,outputs], 
                      derivations = [t], 
                      arbitrary = params
                     ):
LD := LeadingDerivative(IOeqs, Rin):

inputs_maxorders := [seq([FactorDerivative(v, R)], v in LD)]:

alg_subs := {seq(outputs_maxorders[j][2] = Y[j,0], j = 1..numelems(outputs)),
                 seq(seq(diff(outputs_maxorders[j][2], t$i) = Y[j,i], 
                         i = 1 .. degree(outputs_maxorders[j][1])
                    ), j = 1 .. numelems(outputs)
                 ),
              seq(inputs_maxorders[j][2] = U[j,0], j = 1..numelems(inputs)),
                 seq(seq(diff(inputs_maxorders[j][2], t$i) = U[j,i], 
                         i = 1 .. degree(inputs_maxorders[j][1])
                    ), j = 1 .. numelems(inputs)
                 )
            }:

eq_alg := expand(subs(alg_subs, IOeqs)):

#lists of initials and separants to compute the colon ideal
sep := subs(alg_subs, Separant(RG)[-numelems(outputs)..-1]):
ini := subs(alg_subs, Initial(RG)[-numelems(outputs)..-1]):
H_E := mul(In, In in {op(ini)} union {op(sep)}):

# Computation of the colon ideal
Y_vars := indets(eq_alg) minus {op(params)}:
#E := EliminationIdeal(<op(eq_alg), 1 - w * H_E, parameters = params>, Y_vars):

#Egens := simplify(IdealInfo[Generators](E)):

#Temporary assignment to avoid recomputing Egens every run
Egens := [(k6+Y[2,0])*Y[2,1]+k5*Y[2,0],
(((k5-k7-Y[1,1])^2*Y[2,0]+k6*(k5*Y[2,1]+k7^2+2*k7*Y[1,1]+Y[1,1]^2))*Y[1,0]^2+2*(k8+1/2*k10)*((k5-Y[1,1])*(k5-k7-Y[1,1])*Y[2,0]+k6*(k5*Y[2,1]+k7*Y[1,1]+Y[1,1]^2))*Y[1,0]+((k5-Y[1,1])^2*Y[2,0]+k6*(k5*Y[2,1]+Y[1,1]^2))*k8*(k8+k10))*k9+k10*(k7*(k5*Y[2,1]-k6*Y[1,2]-Y[1,2]*Y[2,0]+Y[2,1]^2)*Y[1,0]+((-k5-k7)*Y[1,1]+k5^2)*(k5-Y[1,1])*Y[2,0]+(k7*Y[1,1]^2-2*k5*Y[2,1]*Y[1,1]+k5*Y[2,1]*(k5-Y[2,1]))*k6),
k10*k5^2*k7*Y[1,0]*Y[2,1]+((((k8+k10+Y[1,0])*Y[2,1]+(k7+Y[1,1])*Y[1,0]+Y[1,1]*(k8+k10))*((k8+Y[1,0])*Y[2,1]+(k7+Y[1,1])*Y[1,0]+k8*Y[1,1])*k9-(Y[2,1]^3+2*Y[1,1]*Y[2,1]^2-Y[1,1]*(k7-Y[1,1])*Y[2,1]+k7*(Y[1,0]*Y[1,2]-Y[1,1]^2))*k10)*k6+2*k10*k7*Y[1,0]*Y[2,1]^2)*k5+k10*k7*Y[1,0]*Y[2,1]^3]:

printf("\n==============================================================\n");
printf("The equation(s) defining the corresponding affine variety are:\n\n");
for eq in Egens do printf("%a = 0\n", eq); od;
input_derivatives := seq(inputs_maxorders[j][2], j = 1..numelems(inputs)),
                 seq(seq(diff(inputs_maxorders[j][2], t$i), 
                         i = 1 .. degree(inputs_maxorders[j][1])
                    ), j = 1 .. numelems(inputs)
                 ):
# Compute Lie derivatives of the y-functions that participated in the IO-equations
R2 := DifferentialRing(
                      blocks = [outputs,states,inputs], 
                      derivations = [t], 
                      arbitrary = params
                     ):
eq2 := RosenfeldGroebner(syst, R2):
LieDer := [seq([op(NormalForm(outputs_maxorders[j][2], eq2)),
                 seq(op(NormalForm(diff(outputs_maxorders[j][2], t$i), eq2)), 
                         i = 1 .. degree(outputs_maxorders[j][1]))]
                     , j = 1 .. numelems(outputs)
                 )
            ]:

# Substitute new indeterminates into the state variables in the Lie derivatives
LieDerSubs := subs({seq(states[i](t) = w[i], i = 1 .. numelems(states))}, LieDer):


# Replace the coefficients with new variables 

for i from 1 to numelems(outputs) do
  for j from 1 to degree(outputs_maxorders[i][1])+1 do
      p[i,j] := DecomposePolynomial(expand(numer(LieDerSubs[i][j])), 
                                    [seq(w[s], s = 1 .. numelems(states)), input_derivatives],
                                    params, 
                                    0                
               )[2]:
   od:         
od:
for i from 1 to numelems(outputs) do
  for j from 1 to degree(outputs_maxorders[i][1])+1 do
      pden[i,j] := DecomposePolynomial(expand(denom(LieDerSubs[i][j])), 
                                    [seq(w[s], s = 1 .. numelems(states)), input_derivatives],
                                    params, 
                                    0                
               )[2]:
   od:         
od:

LieDerIndet := [seq([seq((add(
                             p[i,j][s] * f[i,j,s], 
                             s = 1 .. numelems(p[i,j])
                            ))/(add(
                             pden[i,j][s] * fd[i,j,s], 
                             s = 1 .. numelems(pden[i,j])
                            )), 
                          j = 1..degree(outputs_maxorders[i][1])+1
                         )
                     ], 
                     i = 1..numelems(outputs)
                    )
                 ]:

# We now substitute for the coefficients of the outputs (we make additional substitutions to reduce the amount of computation)
LieDerIndet := subs([f[1,1,1] = 1, f[2,1,1] = 1, fd[1,1,1] = 1, fd[2,1,1] = 1, f[2, 2, 1] = -k5, fd[2, 2, 2] = 1, fd[2, 2, 1]=k6, fd[1, 2, 1] = 1, fd[1, 2, 2] = 0, fd[1, 2, 3] = k6, f[1, 2, 1] = k5 - k7, f[1, 2, 2] = k7, f[1,2,4] = -k6 * k7], LieDerIndet):
LieDerIndet := subs(alg_subs, LieDerIndet):
printf("\n==============================\n");
for i from 1 to numelems(outputs) do
  printf("\The Lie derivatives for %a are:\n\n", outputs_maxorders[i][2]);
  for LDer in LieDer[i] do printf("%a\n\n", LDer) od;
od;
printf("\n==============================================================\n");
for i from 1 to numelems(outputs) do
  printf("The Lie derivatives with undertermined coefficients for %a are:\n\n", outputs_maxorders[i][2]);
  for LDer in LieDerIndet[i] do printf("%a\n\n", LDer) od;
od;
# Creating a sample parametrization based on the original equations. 
# The expressions with k's are replaced with undetermined coefficients f's.
# The equations below were obtained by calculating Lie derivatives of y1 and y2
subslist:= [seq([seq(
                    Y[i,j-1] = LieDerIndet[i][j], 
                    j = 1..degree(outputs_maxorders[i][1])+1
                   )], 
                i = 1..numelems(outputs)
                )
            ]:

eq_f := expand(subs(Flatten(subslist), Egens)):

# Solving for the undetermined coefficients the f's after subsituting into the input-output equations
# We first collect the coefficients
cf := map(coeffs, expand(numer(eq_f)), [seq(w[i], i = 1..numelems(states)), input_derivatives]):

fvarsandparams := indets(cf):

printf("\n======================================\n");
printf("The polynomial equations to solve are:\n\n"):
#for cfs in cf do printf("%a = 0\n", cfs); od;

#extract the f-variables

vars := [op(fvarsandparams minus {op(params)})]:
sols := solve([op(cf), fd[1,3,1] = 1], vars):
printf("\n================");
for i from 1 to numelems(sols) do 
  printf("\n Solution #%a is:\n\n", i);
  for sol in sols[i] do printf("%a\n", sol); od;
od;


sol_num := 1:
printf("\nWe pick solution #%a\n", sol_num):
h := subs(sols[sol_num], [seq(map(rhs, subslist[i]), i = 1..numelems(outputs))]):

printf("\n=================================================\n");
for i from 1 to numelems(outputs) do
  printf("The resulting Lie derivatives for variable %a are:\n\n", outputs[i]):
  for hh in h[i] do printf("%a\n", hh); od;
od;

alg_subs_rev := {seq(rhs(ex) = lhs(ex), ex in alg_subs)}:
# Computing the state-space form ODEs for the f's calculated above


with(VectorCalculus):
with(LinearAlgebra):
with(ArrayTools):

xvars := [op(indets(h) minus fvarsandparams minus {t})]:

#patch for inputs

h_u_der_temp := [seq(h[i][2..-1], i=1..numelems(outputs))]:
for s from 1 to numelems(outputs) do
  for S from 2 to numelems(h[s])-1 do
     h_u_der_temp[s][S]  -= add(
           add(
                diff(h[s][S], U[j,i])*U[j,i+1],
                i=0..degree(inputs_maxorders[j][2])
               ), 
               j = 1..numelems(inputs)
           );
   od:  
od:


dH := Concatenate(1, seq(Jacobian(h[i][1..-2], xvars), i = 1..numelems(outputs))):
H := Concatenate(1, seq(convert(h_u_der_temp[i], Vector), i = 1..numelems(outputs))):

reparam :=  convert(simplify(LinearSolve(dH, H)), list):
reparam := subs(alg_subs_rev, reparam):

printf("\n=================================\n");
printf("The reparametrized ODE system is:\n\n");
for i from 1 to numelems(reparam) do printf("w[%a]' = %a\n", i, simplify(reparam[i])); od;

# Since there are many solutions, we now pick a solution, trying to make it look simpler
additional_subs1 := {}:
for i from 1 to numelems(reparam) do 
   new_diffeq[i] := expand(simplify(subs(additional_subs1, reparam[i]), symbolic)): 
od:

# Comparison of the parametrizations: we set the old and new Lie derivatives for y, y',... equal to# each other and solve of the x-variables using GB 
conv := simplify(subs(additional_subs1, Flatten(h)) - 
                                      subs(
                                          {seq(states[i](t) = states[i], i = 1 .. numelems(states))                                            }, 
                                           subs(alg_subs,Flatten(LieDer)) )):

B := Groebner[Basis](numer(conv), plex(op(xvars), op(states))):
ChangeVars := subs(alg_subs_rev, solve(B, xvars)[1]):
printf("\n=========================================\n");
printf("The corresponding change of variables is:\n\n");
for i from 1 to numelems(ChangeVars) do printf("%a\n",ChangeVars[i]); od;

# Checking the result by recomputing the input-output equations
# and making sure that these are the same as the original input-output equations
for j from 1 to numelems(reparam) do 
   new_diffeq_t[j] := subs({seq(w[i] = w[i](t), i = 1..numelems(reparam))}, new_diffeq[j]) 
od:
ChangeVarsRev := [seq(rhs(ChangeVars[i]) = lhs(ChangeVars[i]), i = 1..numelems(ChangeVars))]:
outputequations := subs(ChangeVarsRev, syst[-numelems(outputs)..-1]):
syst_new := [seq(
                  diff(w[i](t), t) - new_diffeq_t[i], 
                  i = 1..numelems(reparam)
                ),
             op(outputequations)  
            ]:
R2 := DifferentialRing(
                      blocks = [xvars, outputs,inputs], 
                      derivations = [t], 
                      arbitrary = params
                     ):
eq := Equations(RosenfeldGroebner(syst_new, R2))[1]:

printf("\n======================================================================\n");
printf("Checking if the new IO-equations are the same as the old IO-equations:\n\n"):
for i from 1 to numelems(outputs) do printf("%a\n", evalb(simplify(eq[-i] - IOeqs[numelems(outputs)-i+1])= 0)): od;
# The following code to simplify the generators of identifiable functions is taken from
# https://github.com/pogudingleb/AllIdentifiableFunctions 

with(PolynomialIdeals):

#------------------------------------------------------------------------------

FieldToIdeal := proc(gens)
    # Input: generators of a subfield of the field of rational functions
    # Computes the MSQ ideal of the field with the new variables of the form x_aux
    # See: https://mediatum.ub.tum.de/doc/685465/document.pdf Definition 2.16
    #      https://doi.org/10.1016/j.jsc.2005.09.010          Lemma 2.1
    local all_vars, subs_dupl, all_dupl, common_denom, polys, f, gb:
    all_vars := indets(gens):
    subs_dupl := map(v -> v = cat(v, _aux), all_vars):
    all_dupl := sort([op(map(v -> subs(subs_dupl, v), all_vars))]):
    common_denom := 1:
    polys := []:
    for f in gens do
        common_denom := lcm(common_denom, denom(f)):
        polys := [op(polys), numer(f) * subs(subs_dupl, denom(f)) - subs(subs_dupl, numer(f)) * denom(f)]:
    end do:
    gb := Groebner[Basis]([op(polys), subs(subs_dupl, common_denom) * t - 1], tdeg(t, op(all_dupl))):
    gb := Groebner[Walk](gb, tdeg(t, op(all_dupl)), lexdeg([t], [op(all_dupl)])):
    gb := select(p -> not (t in indets(p)), gb):
    return PolynomialIdeal(gb, variables=all_dupl):
end proc:

#------------------------------------------------------------------------------


FilterGenerators := proc(ideal)
    # Input: ideal over a rational function field
    # Computes a simplified set of generators of the field of definition
    local gb, gens, p, cf, lc, gsorted, result, big_ideal, cur_ideal, g, new_ideal:
    gb := Groebner[Basis](ideal, tdeg(op(IdealInfo[Variables](ideal)))):
    gens := {}:
    for p in gb do
        cf := sort([coeffs(p, IdealInfo[Variables](ideal))], (a, b) -> length(convert(a, string)) < length(convert(b, string))):
        lc := cf[1]:
        cf := map(c -> c / lc, cf):
        gens := {op(gens), op(cf[2..nops(cf)])}:
    end do:
    gsorted := sort([op(gens)], (a, b) -> length(convert(a, string)) < length(convert(b, string)));
    result := {}:
    big_ideal := FieldToIdeal(gens):
    cur_ideal := FieldToIdeal(result):
    for g in gsorted do
        if big_ideal = cur_ideal then
            return result:
        end if:
        new_ideal := FieldToIdeal({op(result), g}):
        if new_ideal <> cur_ideal then
            # a dirty hack to transform -1/a to a
            if convert(g, string)[1] = "-" then
                g := -g:
            end:
            if convert(g, string)[1] = "1" then
                g := 1 / g:
            end:
            result := {op(result), g}:
            cur_ideal := new_ideal:
        end if:
    end do:
    return result:
end proc:


# Compute a set of generators of the IO-identifiable functions (with simplification)
coefs := coeffs(expand(IOeqs[1]),[diff(y2(t), t, t), diff(y2(t), t), y1(t), y2(t)]):
cfs := coeffs(expand(IOeqs[1]/coefs[1]),[diff(y2(t), t, t), diff(y2(t), t), y1(t), y2(t)]):
printf("================================================\n"):
printf("= Generators of IO-identifiable functions are: =\n\n"):
IOIdentifiableFunctions := map(simplify,FilterGenerators(FieldToIdeal([cfs]))):
for g in IOIdentifiableFunctions do printf("%a\n", g): od:

printf("\n= We immediately see that the coefficients of new ODE #1 and #2 =\n"):
printf("= are IO-identifiable                                           =\n"):

# The coefficient list of new ODE #3:
cflist := simplify([coeffs(expand(simplify((w[2]+w[3])*subs(fd[1,2,2] = 0, ((w[2]+w[3]+fd[1,2,2])*(k8-w[3]-fd[1,2,2])*(k8+k10-w[3]-fd[1,2,2])*k9+k10*k7*w[2])/k10/(w[2]+w[3]+fd[1,2,2])))),[w[1],w[2],w[3]])]):
printf("\n= The coefficients of new ODE #3 are: =\n\n"):
for g in cflist do printf("%a\n", g): od:

# Checking if each coefficient of the third new ODE belongs to the field
# of IO-identifiable functions:
printf("\n= The coefficients of new ODE #3 are IO-identifiable = \n\n"):
for cf in cflist do printf("%a\n", IdealContainment(FieldToIdeal([cf]), FieldToIdeal(IOIdentifiableFunctions))); od;

