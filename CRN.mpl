
restart:
printf("\n=====================================\n");
printf("= Software demo for the CRN example =\n");
printf("=====================================\n\n");

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
      (2*k1 + k4) * x2(t)^2 - (k2 + 2*k6) * x1(t)^2 + (k5-k3)*x1(t)*x2(t),
       -(2*k1 + k4) * x2(t)^2 + (k2 + 2*k6) * x1(t)^2 + (k3-k5)*x1(t)*x2(t)
     ]:
params := [k1,k2,k3,k4,k5,k6]:
states := [x1, x2]:
outputs := [y1]:
output_func := [x1(t)]:
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
printf("The IO-equation is:\n\n %a = 0\n\n", IOeqs[1]);
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
E := EliminationIdeal(<op(eq_alg), 1 - w * H_E, parameters = params>, Y_vars):

Egens := simplify(IdealInfo[Generators](E)):

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

LieDerSubs := subs(alg_subs, LieDerSubs):
# Replace the coefficients with new variables 
seq(
    [seq(
         [coeffs(LieDerSubs[i][j], 
                [seq(w[s], s = 1 .. numelems(states)), op(subs(alg_subs, [input_derivatives]))], 
                p[i][j]
               )], 
         j = 1 .. degree(outputs_maxorders[i][1])+1
        )], 
        i = 1 .. numelems(outputs)
     ):
LieDerIndet := [seq([seq(add(
                             [p[i][j]][s] * f[i,j,s], 
                             s = 1 .. numelems([p[i][j]])
                            ), 
                          j = 1..numelems(p[i])
                         )
                     ], 
                     i = 1..numelems(outputs)
                    )
                 ]:
# We now substitute for the coefficients of the outputs (we do not want to change the outputs)
LieDerIndet := subs([f[1,1,1] = 1, f[2,1,1] = 1], LieDerIndet):
LieDerIndet := subs(alg_subs, LieDerIndet):
printf("\n==============================\n");
for i from 1 to numelems(outputs) do
  printf("\The Lie derivatives for %a are:\n\n", outputs[i]);
  for LDer in LieDer[i] do printf("%a\n", simplify(LDer)) od;
od;
printf("\n==============================================================\n");
for i from 1 to numelems(outputs) do
  printf("The Lie derivatives with undertermined coefficients for %a are:\n\n", outputs[i]);
  for LDer in LieDerIndet[i] do printf("%a\n", simplify(LDer)) od;
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

eq_f := subs(Flatten(subslist), eq_alg):

# Solving for the undetermined coefficients the f's after subsituting into the input-output equations
# We first collect the coefficients

#cf := map(coeffs, expand(eq_f), [seq(w[i], i = 1..numelems(states)), op(subs(alg_subs, [input_derivatives]))]):
cf := map(coeffs, expand(eq_f), [seq(w[i], i = 1..numelems(states))]):
fvarsandparams := indets(cf):

#printf("\n======================================\n");
#printf("The polynomial equations to solve are:\n\n"):
#for cfs in cf do printf("%a = 0\n", cfs); od;

#extract the f-variables

vars := [op(fvarsandparams minus {op(params)})]:
sols := solve([op(cf)], vars):
printf("\n================");
for i from 1 to numelems(sols) do 
  printf("\n Solution #%a is:\n\n", i);
  for sol in sols[i] do printf("%a\n", sol); od;
od;
sol_num := 3:
printf("\nWe pick solution #%a\n and make a substitution into one of the f's to remove the radicals\n", sol_num):
h := subs(sols[sol_num], [seq(map(rhs, subslist[i]), i = 1..numelems(outputs))]):
h := subs([RootOf((2*k1+k4)*_Z^2-f[1,2,3]) = (4*k1 + k3 + 2*k4 - k5)/(2 * k1 + k4)],h):
h := simplify(subs([f[1,2,3] = (4*k1 + k3 + 2*k4 - k5)^2/(2 * k1 + k4)],h)):
printf("\n=================================================\n");
for i from 1 to numelems(outputs) do
  printf("The resulting Lie derivatives for variable %a are:\n\n", outputs[i]):
  for hh in h[i] do printf("%a\n\n", simplify(hh)); od;
od;
alg_subs_rev := {seq(rhs(ex) = lhs(ex), ex in alg_subs)}:
# Computing the state-space form ODEs for the f's calculated above


with(VectorCalculus):
with(LinearAlgebra):
with(ArrayTools):

xvars := [op(indets(h) minus fvarsandparams minus {t})]:

dH := Concatenate(1, seq(Jacobian(h[i][1..-2], xvars), i = 1..numelems(outputs))):
H := Concatenate(1, seq(convert(h[i][2..-1], Vector), i = 1..numelems(outputs))):

reparam :=  convert(simplify(LinearSolve(dH, H)), list):
reparam := subs(alg_subs_rev, reparam):

printf("\n=================================\n");
printf("The reparametrized ODE system is:\n\n");
for i from 1 to numelems(reparam) do printf("w[%a]' = %a\n\n", i, simplify(reparam[i])); od;
# Since there are many solutions, we now pick a solution, trying to make it look simpler
additional_subs1 := {
                     f[1,2,2] = 0 
                    }:

printf("\n=================================================\n");
printf("The reparametrized ODE system with chosen f's is:\n\n");
for i from 1 to numelems(reparam) do 
   new_diffeq[i] := expand(simplify(subs(additional_subs1, reparam[i]), symbolic)): 
   printf("w[%a]' = %a\n\n", i, simplify(new_diffeq[i])); 
od:
# Comparison of the parametrizations: we set the old and new Lie derivatives for y, y',... equal to
# each other and solve of the x-variables using GB 
conv := simplify(subs(additional_subs1, Flatten(h)) - 
                                      subs(
                                          {seq(states[i](t) = states[i], i = 1 .. numelems(states))                                            }, 
                                           subs(alg_subs,Flatten(LieDer)) )):
B := Groebner[Basis](conv, plex(op(xvars), op(states))):
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

