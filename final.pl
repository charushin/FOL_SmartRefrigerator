
% =======================================
% Rules
% =======================================
rule(np(A),[pn(A)]).
rule(np(B),[dt(A^B),n(A)]).
rule(n(A^C),[n(A^B),pp((A^B)^C)]).
rule(n(A),[adj(B^A),n(B)]).

rule(pp(C),[p((A^B)^C),np(A^B)]).
%rule(pp(X^Y),[p(X^Z),np(Z^Y)]).
rule(pp(Z),[p(X^Y^Z),np(X^Y)]).

rule(s(Y),[np(X^Y),vp(X,[])]).
rule(np(B),[num(A^B),n(A)]).

%rule(pp(A^B),[vacp,np(A^B)]).
%rule(vp(X^Y),[
%rule(vp(X^Z,[]),[pv(X^Y,[]),np(Y^Z)]).
%(VP; ..., W H) Ñ (PV; ...) (PP; ... W H)

rule(vp(X^W),[vp(X^Y),pp(Y^W)]).

rule(vp(X^W),[sv(X^Y),s(Y^W)]).
rule(np(X),[prp(X)]).

%contains ham
rule(np((X^P)^exists(X,(and(Q,P)))),[n(X^Q)]).

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

%(RC; φ, [x]) --> REL (S; φ, [x])
%Complement Interrogatives
%(IV; λx.φ, [y]) Ñ (TV; λx.λy.φ, [ ])
rule(iv(X^P,[Y]),[tv(X^Y^P,[])]).
%Subject Interrogatives
%(TV; λy.φ, [x]) Ñ (TV; λx.λy.φ, [ ])
rule(tv(Y^P,[X]),[tv(X^Y^P,[])]).

%%wh question rules
rule(q(Y),[whpr(X^Y),vp(X,[])]).
rule(q(Y^Z),[whpr(X^Y),vp(X^Z,[])]).
rule(ynq(Y),[aux, np(X^Y),vp(X,[])]).

rule(q(Y),[whpr(X^Y),vp(X)]).
rule(q(X),[whpr(X^Y),aux([]),vp(Y)]).

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

%%which milk did sam drink
rule(q(WH),[whpr((A^B)^(C^D)^WH),n(A^B),inv_s(D,[C])]).
%X = q(exists(A, and(milk(A), drink(sam, A))))

%Rules for relative clause
rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).

rule(rc(Y,[X]),[rel,s(Y,[X])]).
rule(rc(Y,[WH]),[rel([]),vp(Y,[WH])]).
rule(rc(Y,[]),[rel([]),vp(Y,[])]).

%(VP; ..., W H) Ñ (PV; ...) (PP; ... W H)
rule(vp(A^B,[WH]),[pv(A^C,[]),pp(C^B,[WH])]).
rule(vp(A^B,[]),[pv(A^C,[]),pp(C^B,[])]).


% =======================================
% Lemmas
% =======================================
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
lemma(apple,n).
lemma(watermelon,n).
lemma(egg,n).
lemma(banana,n).
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
lemma(jane,pn).

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

lemma(expire,iv).
lemma(spoil,iv).
lemma(damage,iv).
lemma(eat,iv).
lemma(drink,iv).
lemma(drank,iv).

lemma(belong,pv).

lemma(slowly,adv).
lemma(quickly,adv).

lemma(did,aux).
lemma(does,aux).
lemma(are,aux).
     
lemma(who,whpr).
lemma(what,whpr).
lemma(which,whpr).
lemma(where,whpr).

lemma(put,dtv).
lemma(gave,dtv).
lemma(give,dtv).
lemma(show,dtv).
lemma(tell,dtv).
lemma(serve,dtv).
lemma(took,dtv).
lemma(take,dtv).
lemma(order,dtv).

lemma(a,dtexists).
lemma(an,dtexists).
lemma(some,dtexists).
lemma(any,dtexists).
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
lemma(of,p).
lemma(under,p).
lemma(in,p).
lemma(inside,p).
lemma(from,p).
lemma(on,vacp).  
lemma(of,vacp).
lemma(at,vacp).
lemma(to,vacp).
lemma(there,vacp).

lemma(that,rel).
lemma(what,rel).
lemma(who,rel).
lemma(which,rel).
lemma(there,rel).

% ==================================
% Lexicon
% ==================================
% 
%Lexicons for performing uninflections to noun, transitive verb and verb with pp complement
lex(n(X^P),Word):- uninflected_noun(Word,Lemma),P =.. [Lemma,X].
lex(tv((X^Y^Z),[]),Word):-uninflected_verb(Word,Lemma),Z=..[Lemma,X,Y].
lex(pv((X^Y^Z),[]),Word):-uninflected_pv(Word,Lemma),Z=..[Lemma,X,Y].

%Noun
lex(n(X^P),Word):- lemma(Word,n), P =.. [Word,X].

%Proper Noun
lex(pn((Word^X)^X),Word):-lemma(Word,pn).

%Adjectives
lex(adj((X^P)^X^and(P,Z)),Word):-lemma(Word,adj), Z =.. [Word,X].

%Transitive Verb
lex(tv((X^Y^Z),[]),Word):-lemma(Word,tv),Z =.. [Word,X,Y].

%Ditransitive Verb
lex(dtv((X^Y^Z^W),[]),Word):-lemma(Word,dtv),W =.. [Word,X,Y,Z].

%Verb having PP complement- rely on
lex(pv((X^Y^Z),[]),Word):-lemma(Word,pv),Z =.. [Word,X,Y].

%Intransitive Verb
lex(iv(X^P),Word):- lemma(Word,iv),P =.. [Word,X].

%Preposition
%handling it as a verb e.g inside
lex(p(X^Y^Z),Word):-lemma(Word,p),Z =.. [Word,X,Y].

%Normal preposition - on,under
lex(p((Y^Z)^Q^(X^P)^and(P,Q)),Word):-lemma(Word,p),Z =.. [Word,X,Y].

%Wh questions
lex(whpr((X^P)^exists(X,and(person(X),P))),who).
lex(whpr((X^P)^exists(X,and(thing(X),P))),what).
lex(whpr((X^P)^(X^Q)^exists(X,and(P,Q))),which).

lex(aux,Word):-lemma(Word,aux).
lex(be,Word):-lemma(Word,be).

lex(vacp,Word):-lemma(Word,vacp).
lex(pp(X^_,[X]),Word):-lemma(Word,vacp).

lex(rel,Word):-lemma(Word,rel).

lex(dt((X^P)^(X^Q)^exists(X,and(P,Q))),Word):-lemma(Word,dtexists).
lex(dt((X^P)^(X^Q)^the(X,and(P,Q))),Word):-lemma(Word,dtthe).
lex(dt((X^P)^(X^Q)^not(exists(X,and(P,Q)))),Word):-lemma(Word,dtno).
lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),Word):-lemma(Word,dtforall).

lex(num((X^P)^(X^Q)^Z),Word):-lemma(Word,num),Z=.. [Word,X,and(P,Q)].

%For handling inflection
uninflected_noun(Word,Lemma):-member(A,['',es,ed,s,ing]),atom_concat(Lemma,A,Word),lemma(Lemma,n).
uninflected_verb(Word,Lemma):-member(A,['',es,ed,s,ing]),atom_concat(Lemma,A,Word),lemma(Lemma,tv).
uninflected_pv(Word,Lemma):-member(A,['',es,ed,s,ing]),atom_concat(Lemma,A,Word),lemma(Lemma,pv).



%sr_parse([every,blue,container,on,the,top,shelf,contains,a,sandwich,that,has,no,meat],X).
%X = s(forall(A, imp(and(and(container(A), blue(A)), the(B, and(and(shelf(B), top(B)), on(A, B)))), exists(C, and(and(sandwich(C), not(exists(D, and(meat(D), has(C, D))))), contain(A, C))))), [])

%sr_parse([every,white,container,on,the,bottom,shelf,contains,a,banana],X).
%X = s(forall(A, imp(and(and(container(A), white(A)), the(B, and(and(shelf(B), bottom(B)), on(A, B)))), exists(C, and(banana(C), contain(A, C))))), [])

%sr_parse([what,does,the,yellow,bowl,on,the,middle,shelf,contain],X).
%X = q(exists(A, and(thing(A), the(B, and(and(and(bowl(B), yellow(B)), the(C, and(and(shelf(C), middle(C)), on(B, C)))), contain(B, A))))))

%sr_parse([are,there,two,watermelons,in,the,fridge],X).
%X = ynq(two(A, and(and(watermelon(A), the(B, and(fridge(B), in(A, B)))), C)))

%sr_parse([is,there,milk],X).
%X = ynq(exists(A, and(milk(A), B)))

%sr_parse([who,drank,the,almond,milk],X).
%X = q(exists(A, and(person(A), the(B, and(and(milk(B), almond(B)), drank(A, B))))))

%sr_parse([which,milk,did,sam,drink],X).
%X = q(exists(A, and(milk(A), drink(sam, A))))

%sr_parse([is,there,an,empty,box,of,popsicles,inside,the,freezer]).
%X = ynq(exists(A, and(and(and(and(box(A), empty(A)), exists(B, and(popsicles(B), of(A, B)))), the(C, and(freezer(C), inside(A, C)))), D)))

%sr_parse([a,blue,box,contains,some,ham],X).
%X = s(exists(A, and(and(box(A), blue(A)), exists(B, and(ham(B), contain(A, B))))), [])

%sr_parse([a,blue,box,contains,ham],X).
%X = s(exists(A, and(and(box(A), blue(A)), exists(B, and(ham(B), contain(A, B))))), [])

%sr_parse([the,white,box,that,the,freezer,contains,belongs,to,sue],X).
%X = s(the(A, and(and(and(box(A), white(A)), the(B, and(freezer(B), contain(B, A)))), belong(A, sue))), [])

%sr_parse([is,there,an,egg,inside,the,blue,box],X).
%X = ynq(exists(A, and(and(egg(A), the(B, and(and(box(B), blue(B)), inside(A, B)))), C)))

%sr_parse([are,there,two,eggs,inside,the,blue,box],X).
%X = ynq(two(A, and(and(egg(A), the(B, and(and(box(B), blue(B)), inside(A, B)))), C)))

%sr_parse([what,does,the,green,box,contain],X).
%X = q(exists(A, and(thing(A), the(B, and(and(box(B), green(B)), contain(B, A))))))

%sr_parse([who,put,every,yellow,box,on,the,white,bowl],X).
%X = q(exists(A, and(person(A), forall(B, imp(and(box(B), yellow(B)), the(C, and(and(bowl(C), white(C)), put(A, B, C))))))))


%Not parsing
%is,there,a,sandwich,that,does,not,contain,meat


% ===========================================================
% Main loop:
% 1. Repeat "input-response" cycle until input starts with "bye"
%    Each "input-response" cycle consists of:
%     1.1 Reading an input string and convert it to a tokenized list
%     1.2 Processing tokenized list
% ===========================================================

chat:-
 repeat,
   readinput(Input),
   process(Input), 
  (Input = [bye| _] ),!.
  

% ===========================================================
% Read input:
% 1. Read char string from keyboard. 
% 2. Convert char string to atom char list.
% 3. Convert char list to lower case.
% 4. Tokenize (based on spaces).
% ===========================================================

readinput(TokenList):-
   read_line_to_codes(user_input,InputString),
   string_to_atom(InputString,CharList),
   string_lower(CharList,LoweredCharList),
   tokenize_atom(LoweredCharList,TokenList).


% ===========================================================
%  Process tokenized input
% 1. Parse morphology and syntax, to obtain semantic representation
% 2. Evaluate input in the model
% If input starts with "bye" terminate.
% ===========================================================

process(Input):-
  parse(Input,SemanticRepresentation),
  modelchecker(SemanticRepresentation,Evaluation),
  respond(Evaluation),!,
  nl,nl.
  
process([bye|_]):-
   write('> bye!').


% ===========================================================
%  Parse:
% 1. Morphologically parse each token and tag it.
% 2. Add semantic representation to each tagged token
% 3. Obtain FOL representation for input sentence
% ===========================================================



% =======================================
% Shift-Reduce Parse 
% =======================================

parse(Sentence, SentenceRepr):-
        srparse([],SentenceRepr,Sentence).
 
srparse([X],X,[]).


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


% ==================================================
% A simple model
% ==================================================

model([a,b,c,p,f,g],
           [
           [empty,[c]],
           [box,[a,c]],
           [thing,[a,b,c,p]],
           [good,[b]],
           [ham,[b]],
           [egg,[f,g]],
           [popsicle,[p]],
           [contain, [[a,b],[c,b],[a,f],[a,g]]],
           [of,[[c,p]]],
           [in,[[f,a],[g,a]]]
           ]).





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




%=================================================
%model checker
%-===========================
modelchecker(s(SemanticRepresentation), Evaluation):-
  sat([],s(SemanticRepresentation),Temp)->Evaluation=Temp; Evaluation=[not_true_in_the_model]. 
  %the last condition is when the sat returns false

modelchecker(ynq(SemanticRepresentation), Evaluation):-
  sat([],ynq(SemanticRepresentation),Temp)->Evaluation = Temp; Evaluation=[no_to_question]. 
  %the last condition is when the sat returns false

modelchecker(q(SemanticRepresentation), Evaluation):-
  sat([], q(SemanticRepresentation), [_,[_,Temp]]),
  model(_,G),
  findall(C,(member(C,G)), SecondList),
  findall(D,(member([D,Second],SecondList), member(Temp,Second), 
  \+(D==thing)),Evaluation).

%===================================================
% New rules
%===================================================


%sat rules for assertion of sentences

%calling sat from the start
sat(G,s(Formula),Result):-
  sat(G,Formula, Temp), 
  (Temp==[]-> Result=[not_true_in_the_model];Result=[true_in_the_model]).

sat(G,s(the(X,Formula)),Result):-
  sat(G,exists(X,Formula), Temp),
  (Temp==[]-> Result=[not_true_in_the_model];Result=[true_in_the_model]). 


%rules for yes or no question

sat(G,ynq(Formula),Result):-
  sat(G,Formula, Temp), 
  (Temp==[]-> Result=[no_to_question];Result=[yes_to_question]).

sat(G,ynq(the(X,Formula)),Result):-
  sat(G,exists(X,Formula), Temp),
  (Temp==[]-> Result=[no_to_question];Result=[yes_to_question]).


sat(G, q(Formula), Result):-
  sat(G, Formula, Result).

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


%======================================
%additional rule i feel was required
%======================================
sat(G, the(X,Formula), Result):-
  sat(G,exists(X,Formula), Result).

%========================================
% Rules for numerals
%========================================


%number one
sat(G1,one(X,Formula),Result):-
  findall(_, sat(G1, exists(X,Formula), _), Result),
  length(Result, Length), Length>=1.

%number two
sat(G1,two(X,Formula),Result):-
  findall(_, sat(G1, exists(X,Formula), _), Result),
  length(Result, Length), Length>=2.

%number three
sat(G1,two(X,Formula),Result):-
  findall(_, sat(G1, exists(X,Formula), _), Result),
  length(Result, Length), Length>=3.

%number four
sat(G1,two(X,Formula),Result):-
  findall(_, sat(G1, exists(X,Formula), _), Result),
  length(Result, Length), Length>=4.

%number five
sat(G1,two(X,Formula),Result):-
  findall(_, sat(G1, exists(X,Formula), _), Result),
  length(Result, Length), Length>=5.

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
respond(Evaluation):-
  findall(_,(member(Adj,Evaluation),lemma(Adj,adj), write(Adj),write(' ')),_),  
  findall(_,(member(Noun,Evaluation),lemma(Noun,B),member(B,[n,pn]),write(Noun)),_).       

% wh-interrogative false in the model
 respond(Evaluation) :- 
    Evaluation = [i_dont_know],      
    write('I dont know').
             


