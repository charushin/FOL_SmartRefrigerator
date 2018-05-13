
% __________________________________________________
%
%             MODEL CHECKER (closed world assumption)
% __________________________________________________



% ==================================================
% A simple model
% ==================================================

model([a,b,c,d],
           [
             [blue, [c]], 
             [box,[c]], 
             [thing, [c,d]], 
             [ham,[d]],
             [sam, [a]], 
             [person,[a]], 
             [almond, [b]],
             [milk, [b]], 
             [drink, [[a,b]]], 
             [contain,[[c,d]]] 
           ]).


%===========Model Checker==========

modelchecker(SemanticRepresentation, Evaluation):-
sat([], SemanticRepresentation, Evaluation).

% ==================================================
% Function i
% Determines the value of a variable/constant in an assignment G
% ==================================================

i(Var,G,Value):- 
    var(Var),
    member([Var2,Value],G), 
    Var == Var2.   

i(C,_,Value):- 
   nonvar(C),
   f(C,Value).


% ==================================================
% Function F
% Determines if a value is in the denotation of a Predicate/Relation
% ==================================================

f(Symbol,Value):- 
   model(_,F),
    member([Symbol,ListOfValues],F), 
    member(Value,ListOfValues).  


% ==================================================
% Extension of a variable assignment
% ==================================================

extend(G,X,[ [X,Val] | G]):-
   model(D,_),
   member(Val,D).



%======================
%New sat rules
%======================

sat(G1, s(Formula), G3) :-
  sat(G1, Formula, G),
  (G==[]-> G3=[not_true_in_the_model];G3=[true_in_the_model]).


sat(G1, ynq(Formula), G3):-
  sat(G1,Formula, G),
  (G==[]-> G3=[no_to_question];G3=[yes_to_question]).

sat(G1, q(exists(X,Formula)), Result):-
  sat(G1, exists(X, Formula), G3), model(B,G), 
  findall(C, (member(A, G), member([V,C], A), G3 ==[_,[_,V]]), Result).




% ==================================================
% Existential quantifier
% ==================================================

sat(G1,exists(X,Formula),G3):-
   extend(G1,X,G2),
   sat(G2,Formula,G3).


% ==================================================
% Definite quantifier (semantic rather than pragmatic account)
% ==================================================

 sat(G1,the(X,and(A,B)),G3):-
   sat(G1,exists(X,and(A,B)),G3),
   i(X,G3,Value), 
   \+ ( ( sat(G1,exists(X,A),G2), i(X,G2,Value2), \+(Value = Value2)) ).




% ==================================================
% Negation 
% ==================================================

sat(G,not(Formula2),G):-
   \+ sat(G,Formula2,_).

% ==================================================
% Universal quantifier
% ==================================================

sat(G, forall(X,Formula2),G):-
  sat(G,not( exists(X,not(Formula2) ) ),G).


% ==================================================
% Conjunction
% ==================================================

sat(G1,and(Formula1,Formula2),G3):-
  sat(G1,Formula1,G2), 
  sat(G2,Formula2,G3). 


% ==================================================
% Disjunction
% ==================================================


sat(G1,or(Formula1,Formula2),G2):-
  ( sat(G1,Formula1,G2) ;
    sat(G1,Formula2,G2) ).


% ==================================================
% Implication
% ==================================================

sat(G1,imp(Formula1,Formula2),G2):-
   sat(G1,or(not(Formula1),Formula2),G2).


% ==================================================
% Predicates
% ==================================================

sat(G,Predicate,G):-
   Predicate =.. [P,Var],
   \+ (P = not),
   i(Var,G,Value),
   f(P,Value).

% ==================================================
% Two-place Relations
% ==================================================

sat(G,Rel,G):-
   Rel =.. [R,Var1,Var2],
   \+ ( member(R,[exists,forall,and,or,imp,the]) ),
   i(Var1,G,Value1),
   i(Var2,G,Value2),
   f(R,[Value1,Value2]).


