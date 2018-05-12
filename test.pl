rule(np(A),[pn(A)]).
rule(np(B),[dt(A^B),n(A)]).
rule(n(A^C),[n(A^B),pp((A^B)^C)]).
rule(n(A),[adj(B^A),n(B)]).

rule(pp(C),[p(A^B^C),np(A^B)]).
rule(vp(A),[iv(A)]).
%rule(vp(A^B),[tv(A^C),np(C^B)]).
%rule(s(B),[np(A^B),vp(A)]).




rule(s(Y),[np(X^Y),vp(X,[])]).



%rule(pv(X^Y,[]),[tv(X^Y,[]),vacp]).
%rule(vp(X^Z,[]),[pv(X^Y,[]),np(Y^Z)]).
%rule(pp(A^B),[vacp,np(A^B)]).
%rule(vp(X^Y),[
%rule(vp(X^Z,[]),[pv(X^Y,[]),np(Y^Z)]).
%(VP; ..., W H) Ñ (PV; ...) (PP; ... W H)


rule(vp(X^W^Z),[dtv(X^Y^Y1),np(Y^W),np(Y1^Z)]).
rule(vp(X^W),[vp(X^Y),pp(Y^W)]).

rule(vp(X^W),[sv(X^Y),s(Y^W)]).
rule(np(X),[prp(X)]).

rule(np((X^P)^exists(X,(and(P,Q)))),[n(X^Q)]).

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

%New Verbal Rules
rule(vp(K,[WH]),[tv(Y,[WH]),np(Y^K)]).
rule(s(X,[WH]),[vp(X,[WH])]).

%%wh question rules
rule(q(Y),[whpr(X^Y),vp(X,[])]).
rule(ynq(Y),[aux, np(X^Y),vp(X,[])]).
%rule(ynq(Y),[aux,s(Y)]).
rule(q(Z),[whpr((X^Y)^Z), inv_s(Y,[X])]).
rule(inv_s(Y,[WH]),[aux, np(X^Y),vp(X,[WH])]).

rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).

%rule(rc(X,[Y]),[rel(_,X,[Y])]).
rule(rc(Y,[X]),[rel,s(Y,[X])]).
%rule(rc(Y),[rel([]),vp(Y)]).
%rule(rc(Y,[]),[rel([]),vp(Y,[])]).

%(VP; ..., W H) Ñ (PV; ...) (PP; ... W H)
rule(vp(A^B,[WH]),[pv(A^C,[]),pp(C^B,[WH])]).


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
lemma(ate,tv).     
lemma(contain,tv).


lemma(belong,pv).
lemma(belongs,pv).
lemma(belonged,pv).


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




lemma(a,dtexists).
lemma(an,dtexists).
lemma(some,dtexists).
lemma(the,dtthe).
lemma(each,dtforall).
lemma(all,dtforall).
lemma(every,dtforall).
lemma(no,dtno).

lemma(is,be).
lemma(are,be).
lemma(does,be).
lemma(was,be).
lemma(eat,tv).

lemma(on,p).
lemma(under,p).
lemma(on,vacp).  
lemma(of,vacp).
lemma(at,vacp).
lemma(to,vacp).





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
lex(tv((X^Y^Z),[]),Word):-lemma(Word,tv),Z =.. [Word,X,Y].
lex(pv((X^Y^Z),[]),Word):-lemma(Word,pv),Z =.. [Word,X,Y].

lex(iv(X^P),Word):- lemma(Word,iv),P =.. [Word,X].

lex(whpr((X^P)^exists(X^and(person(X)),P)),who).

lex(aux,does).
lex(aux,did).
lex(aux,Word):-lemma(Word,aux).

lex(vacp,Word):-lemma(Word,vacp).
lex(pp(X^P,[X]),Word):-lemma(Word,vacp).

lex(whpr((X^P)^exists(X^and(thing(X)),P)),what).



lex(rel,that).

lex(p((Y^in(X,Y))^Q^(X^P)^and(P,Q)),in).

lex(p((Y^on(X,Y))^Q^(X^P)^and(P,Q)),on).



lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),Word):-lemma(Word,dtexists).
lex(dt((X^P)^(X^Q)^the(X,(and(P,Q)))),Word):-lemma(Word,dtthe).
lex(dt((X^P)^(X^Q)^not(X,(and(P,Q)))),Word):-lemma(Word,dtno).
lex(dt((X^P)^(X^Q)^forall(X,(imp(P,Q)))),Word):-lemma(Word,dtforall).





%lex(tv((X^Y^Z),[]),Word):-name(Word,Word1),prefix(W,Word1),name(W1,W),lemma(W1,tv),Z =.. [W1,X,Y].

%lex(n(X^P),Word):- uninflected_word(Word,Lemma),P =.. [Lemma,X].
lex(tv((X^Y^Z),[]),Word):-uninflected_word(Word,Lemma),Z=..[Lemma,X,Y].

uninflected_word(Word,Lemma):-member(A,['',es,ed,s,ing]),atom_concat(Lemma,A,Word),lemma(Lemma,_).

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


