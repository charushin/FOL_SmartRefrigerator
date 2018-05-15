rule(np(A),[pn(A)]).
rule(np(B),[dt(A^B),n(A)]).
rule(n(A^C),[n(A^B),pp((A^B)^C)]).
rule(n(A),[adj(B^A),n(B)]).

rule(pp(C),[p(A^B^C),np(A^B)]).

%rule(pp(C[]),[p(A^B^C,[]),np(A^B)]).
rule(pp(X^Y),[p(X^Z),np(Z^Y)]).



rule(s(Y),[np(X^Y),vp(X,[])]).
rule(np(B),[num(A^B),n(A)]).



%rule(pp(A^B),[vacp,np(A^B)]).
%rule(vp(X^Y),[
%rule(vp(X^Z,[]),[pv(X^Y,[]),np(Y^Z)]).
%(VP; ..., W H) Ñ (PV; ...) (PP; ... W H)



rule(vp(X^W),[vp(X^Y),pp(Y^W)]).

rule(vp(X^W),[sv(X^Y),s(Y^W)]).
rule(np(X),[prp(X)]).

rule(np((X^P)^exists(X,(and(Q,P)))),[n(X^Q)]).

rule(q(Y),[whpr(X^Y),vp(X)]).
rule(q(X),[whpr(X^Y),aux([]),vp(Y)]).

%(RC; φ, [x]) --> REL (S; φ, [x])
%Complement Interrogatives
%(IV; λx.φ, [y]) Ñ (TV; λx.λy.φ, [ ])
rule(iv(X^P,[Y]),[tv(X^Y^P,[])]).
%Subject Interrogatives
%(TV; λy.φ, [x]) Ñ (TV; λx.λy.φ, [ ])
rule(tv(Y^P,[X]),[tv(X^Y^P,[])]).

%Revised Verbal rules
rule(vp(X^K,[]),[tv((X^Y),[]),np(Y^K)]).
rule(vp(X,WH),[iv(X,WH)]).
rule(s(Y,WH),[np(X^Y),vp(X,WH)]).
%Ditransitive

%New Verbal Rules
rule(vp(K,[WH]),[tv(Y,[WH]),np(Y^K)]).
rule(s(X,[WH]),[vp(X,[WH])]).


% Rule for Ditransitive verb
% VP -> DTV NP NP
rule(vp(X^A,[]),[dtv(X^Y^Z^W,[]),np((Y^B)^A),np((Z^W)^B)]).


%%wh question rules
rule(q(Y),[whpr(X^Y),vp(X,[])]).
rule(q(Y^Z),[whpr(X^Y),vp(X^Z,[])]).
rule(ynq(Y),[aux, np(X^Y),vp(X,[])]).

%rule(ynq(Y),[be,rel,np(X^Y),vp(X,[])]).
rule(np(X),[vacp,np(X)]).
rule(np(X),[rel,np(X)]).
%is there a sandwich that contains some meat
rule(ynq(Z),[be,np(_^Z)]).
%rule(ynq(Y),[be,rel,np(X^Y),pp(X,[Y])]).
%is there an egg inside the blue box
rule(ynq(Z),[be,np(X^Z),pp(X)]).
%rule(ynq(Y),[aux,s(Y)]).
rule(q(Z),[whpr((X^Y)^Z), inv_s(Y,[X])]).

rule(inv_s(Y,[WH]),[aux, np(X^Y),vp(X,[WH])]).

%lex(whpr((X^P)^exists(X^and(thing(X)),P)),which).
%rule(q(WH)^^[whpr(A^and(A^N1,A^WH)),n(A^N1),inv_s(Y,[A])]).

rule(q(A^S),[whpr(B^A),n(B),inv_s(S,[B])]).
%lex(whpr((X^P)^(X^Q)^exists(X,and(P,Q))),which).
%rule(q(),[whpr(),n(X^B),inv(S,[X^B])]).
%rule(q(A,S),[whpr(C^A),n(A^and(B,C)),inv_s(S,[B])]).
%rule(q(Z),[whpr(),n()^,inv_s()]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).


rule(rc(Y,[X]),[rel,s(Y,[X])]).
rule(rc(Y,[WH]),[rel([]),vp(Y,[WH])]).
rule(rc(Y,[]),[rel([]),vp(Y,[])]).


%rule(pv(X,[]),[tv(X,[]),vacp]).
%rule(vp(K,[WH]),[tv(Y,[WH]),np(Y^K)]).
%rule(vp(K,[WH]),[pv(Y,[WH]),np(Y^K)]).

%(VP; ..., W H) Ñ (PV; ...) (PP; ... W H)
rule(vp(A^B,[WH]),[pv(A^C,[]),pp(C^B,[WH])]).
rule(vp(A^B,[]),[pv(A^C,[]),pp(C^B,[])]).


lemma(box,n).
lemma(ham,n).
lemma(container,n).
lemma(refrigerator,n).
lemma(shelf,n).
lemma(fridge,n).
lemma(milk,n).
lemma(bowl,n).
lemma(freezer,n).
lemma(sandwich,n).
lemma(popsicles,n).
lemma(fruit,n).
lemma(meat,n).
lemma(watermelon,n).
lemma(egg,n).
lemma(banana,n).
lemma(almond,n).
lemma(soy,n).
lemma(boy,n).

lemma(one,num).
lemma(two,num).
lemma(three,num).
lemma(four,num).
lemma(five,num).
lemma(six,num).
lemma(seven,num).
lemma(eight,num).
lemma(nine,num).
lemma(ten,num).
lemma(zero,num).


lemma(sam,pn).
lemma(tom,pn).
lemma(mia,pn).
lemma(sue,pn).

lemma(blue,adj).
lemma(yellow,adj).
lemma(black,adj).
lemma(green,adj).
lemma(red,adj).
lemma(white,adj).
lemma(top,adj).
lemma(middle,adj).
lemma(bottom,adj).
lemma(empty,adj).
lemma(full,adj).

lemma(almond,adj).
lemma(skim,adj).
lemma(soy,adj).
lemma(ripe,adj).
lemma(bad,adj).
lemma(good,adj).

lemma(have,tv).
lemma(has,tv).
lemma(has,tv).
lemma(punch,tv).
lemma(drank,tv).

lemma(saw,tv).
lemma(see,tv).
lemma(see,iv).
lemma(eat,tv).
lemma(drank,tv).
lemma(drink,tv).
lemma(ate,tv).     
lemma(contain,tv).
lemma(belong,tv).


lemma(belong,pv).

lemma(slowly,adv).
lemma(quickly,adv).


lemma(did,aux).
lemma(does,aux).
lemma(are,aux).
     
lemma(who,whpr).
lemma(what,whpr).
lemma(who,whpr).
lemma(where,whpr).

lemma(put,dtv).
lemma(there,rel).



lemma(a,dtexists).
lemma(an,dtexists).
lemma(some,dtexists).
lemma(the,dtthe).
lemma(each,dtforall).
lemma(all,dtforall).
lemma(every,dtforall).
lemma(no,dtno).
lemma(not,dtno).


lemma(is,be).
lemma(are,be).
lemma(does,be).
lemma(was,be).
lemma(eat,tv).

lemma(on,p).
lemma(at,p).
lemma(under,p).
lemma(inside,p).
lemma(on,vacp).  
lemma(of,vacp).
lemma(at,vacp).
lemma(to,vacp).
lemma(there,vacp).

lemma(that,rel).
lemma(what,rel).
lemma(who,rel).
lemma(which,rel).



%is,there,an,egg,inside,the,blue,box

% how to define plural and numerals

% ==================================
% Lexicon
% ==================================
% = tv(_G294^_G297^contain(_G294,_G297),[ ])
lex(pn((tom^X)^X),tom).


lex(pn((sue^X)^X),sue).

lex(n(X^P),Word):- lemma(Word,n), P =.. [Word,X].
lex(pn((Word^X)^X),Word):-lemma(Word,pn).
lex(adj((X^P)^X^and(P,Z)),Word):-lemma(Word,adj), Z =.. [Word,X].
%lex(adj((X^P)^X^and(P,Z)),Word):-lemma(Word,num), Z =.. [Word,X].
lex(tv((X^Y^Z),[]),Word):-lemma(Word,tv),Z =.. [Word,X,Y].
lex(dtv((X^Y^Z^W),[]),Word):-lemma(Word,dtv),W =.. [Word,X,Y,Z].

lex(pv((X^Y^Z),[]),Word):-lemma(Word,pv),Z =.. [Word,X,Y].

lex(iv(X^P),Word):- lemma(Word,iv),P =.. [Word,X].
lex(p(X^Y^Z),Word):-lemma(Word,p),Z =.. [Word,X,Y].
lex(p((Y^Z)^Q^(X^P)^and(P,Q)),Word):-lemma(Word,p),Z =.. [Word,X,Y].

lex(whpr((X^P)^exists(X,and(person(X),P))),who).
lex(whpr((X^P)^exists(X,and(thing(X),P))),what).

%lex(whpr((X^P)^exists(X,and(thing(X)),P)),which).
%
lex(whpr((X^P)^(X^Q)^exists(X,and(P,Q))),which).
%lex(whpr((X^P)^(X^Q)^q(X,P,Q)),which).


lex(aux,Word):-lemma(Word,aux).
lex(be,Word):-lemma(Word,be).

lex(vacp,Word):-lemma(Word,vacp).
%lex(p([],Word):-lemma(Word,vacp).
lex(pp(X^_,[X]),Word):-lemma(Word,vacp).



lex(rel,Word):-lemma(Word,rel).

lex(p((Y^in(X,Y))^Q^(X^P)^and(P,Q)),in).

lex(p((Y^on(X,Y))^Q^(X^P)^and(P,Q)),on).



lex(dt((X^P)^(X^Q)^exists(X,and(P,Q))),Word):-lemma(Word,dtexists).
lex(dt((X^P)^(X^Q)^the(X,and(P,Q))),Word):-lemma(Word,dtthe).
lex(dt((X^P)^(X^Q)^not(exists(X,and(P,Q)))),Word):-lemma(Word,dtno).
lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),Word):-lemma(Word,dtforall).

lex(num((X^P)^(X^Q)^Z),Word):-lemma(Word,num),Z=.. [Word,X,and(P,Q)].

%lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),every).





%lex(tv((X^Y^Z),[]),Word):-name(Word,Word1),prefix(W,Word1),name(W1,W),lemma(W1,tv),Z =.. [W1,X,Y].

lex(n(X^P),Word):- uninflected_noun(Word,Lemma),P =.. [Lemma,X].
lex(tv((X^Y^Z),[]),Word):-uninflected_word(Word,Lemma),Z=..[Lemma,X,Y].
lex(pv((X^Y^Z),[]),Word):-uninflected_pv(Word,Lemma),Z=..[Lemma,X,Y].


uninflected_noun(Word,Lemma):-member(A,['',es,ed,s,ing]),atom_concat(Lemma,A,Word),lemma(Lemma,n).
uninflected_word(Word,Lemma):-member(A,['',es,ed,s,ing]),atom_concat(Lemma,A,Word),lemma(Lemma,tv).
uninflected_pv(Word,Lemma):-member(A,['',es,ed,s,ing]),atom_concat(Lemma,A,Word),lemma(Lemma,pv).

% =======================================
% Example: Shift-Reduce Parse 
% =======================================

sr_parse(Sentence, SentenceRepr):-
        srparse([],SentenceRepr,Sentence).
 
sr_parse(X,X,[]).
srparse([X],X,[]):-
  numbervars(X,0,_).


srparse([Y,X|MoreStack],SentenceRepr,Words):-
       rule(LHS,[X,Y]),
       srparse([LHS|MoreStack],SentenceRepr,Words).

srparse([X|MoreStack],SentenceRepr,Words):-
       rule(LHS,[X]),
       srparse([LHS|MoreStack],SentenceRepr,Words).
srparse([Z,Y,X|MoreStack],SentenceRepr,Words):-
       rule(LHS,[X,Y,Z]),
       srparse([LHS|MoreStack],SentenceRepr,Words).

srparse(Stack,SentenceRepr,[Word|Words]):-
        lex(X,Word),
        srparse([X|Stack],SentenceRepr,Words).






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



% ===========================================================
%  Respond
%  For each input type, react appropriately.
% ===========================================================

% Declarative true in the model
respond(Evaluation) :- 
    Evaluation = [true_in_the_model], 
    write('That is correct'),!.

% Declarative false in the model
respond(Evaluation) :- 
    Evaluation = [not_true_in_the_model],  
    write('That is not correct'),!.

% Yes-No interrogative true in the model
respond(Evaluation) :- 
    Evaluation = [yes_to_question],     
    write('yes').

% Yes-No interrogative false in the model   
respond(Evaluation) :- 
    Evaluation = [no_to_question],      
    write('no').

% wh-interrogative true in the model
% ...             

% wh-interrogative false in the model
% ...             


