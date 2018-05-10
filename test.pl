rule(np(A),[pn(A)]).
rule(np(B),[dt(A^B),n(A)]).
rule(n(A^C),[n(A^B),pp((A^B)^C)]).
rule(n(A),[adj(B^A),n(B)]).
rule(np(A),[n(A)]).
rule(pp(C),[p(A^B^C),np(A^B)]).
%rule(vp(A),[iv(A)]).
%rule(vp(A^B),[tv(A^C),np(C^B)]).
%rule(s(B),[np(A^B),vp(A)]).

%Revised Verbal rules
rule(vp(X^K,[]),[tv(X^Y,[]),np(Y^K)]).
rule(vp(X,WH),[iv(X,WH)]).
rule(s(Y,WH),[np(X^Y),vp(X,WH)]).

%New Verbal Rules
rule(vp(K,[WH]),[tv(Y,[WH]),np(Y^K)]).
rule(s(X,[WH]),[vp(X,[WH])]).


rule(vp(X^W^Z),[dtv(X^Y^Y1),np(Y^W),np(Y1^Z)]).
rule(vp(X^W),[vp(X^Y),pp(Y^W)]).
rule(vp(X^W),[sv(X^Y),s(Y^W)]).
rule(np(X),[prp(X)]).


%rule(q(Y),[whpr(X^Y),vp(X)]).
%rule(q(X),[whpr(X^Y),aux([]),vp(Y)]).


%wh question rules
rule(q(Y),[whpr(X^Y),vp(X,[])]).
rule(ynq(Y),[aux, np(X^Y),vp(X,[])]).
rule(q(Z),[whpr((X^Y)^Z), inv_s(Y,[X])]).
rule(inv_s(Y,[WH]),[aux([]), np(X^Y),vp(X,[WH])]).


rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).
%rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).
%rule(rc(X,[Y]),[rel(S,X,[Y])]).
%X^explode(X),[ ]
rule(rc(Y,[]),[rel([]),vp(Y)]).



lemma(box,n).
lemma(ham,n).
lemma(contain,tv).
lemma(a,dt).
lemma(blue,adj).
lemma(bill,pn).
lemma(saw,tv).
lemma(eat,tv).
lemma(did,aux).
lemma(does,aux).
lemma(who,whpr).
lemma(what,whpr).
lemma(punch,tv).
lemma(drank,tv).
lemma(put,dtv).





lemma(box,n).
lemma(container,n).
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


lemma(slowly,adv).
lemma(quickly,adv).


% how to define plural and numerals


%parse([is,there,an,egg,inside,the,blue,box],X).
%X = ynq(exists(_G406,and(egg(_G406),the(_G419,and(box(_G419),blue(_G419
%),contain(_G419,_G406))))))
%?- parse([are,there,two,eggs,inside,the,blue,box],X).
%X = ynq(two(_G406,and(eggs(_G406),the(_G419,and(box(_G419),blue(_G419
%),contain(_G419,_G406))))))
%?- parse([what,does,the,green,box,contain],X).
%X = q(_G386,and(thing(_G386),the(_G394,and(box(_G394),green(_G394)),contain(_G394,_G386))))
%?- parse([who,put,every,yellow,box,on,the,white,bowl],X).
%X = q(_G366,and(person(_G366),forall(_G374,imp(and(box(_G374),yellow(_G374)),
%the(_G367,and(bowl(_G367),white(_G367)),put(_G366,_G374,_G367))))))
% ==================================
% Lexicon
% ==================================
% = tv(_G294^_G297^contain(_G294,_G297),[ ])
lex(pn((tom^X)^X),tom).


lex(pn((sue^X)^X),sue).

lex(n(X^P),Word):- lemma(Word,n), P =.. [Word,X].
lex(pn((Word^X)^X),Word):-lemma(Word,pn).
lex(adj((X^P)^X^and(P,Z)),Word):-lemma(Word,adj), Z =.. [Word,X].
lex(tv(((X^Y)^Z),[]),Word):-lemma(Word,tv),Z =.. [Word,X,Y].

lex(iv(X^P),Word):- lemma(Word,iv),P =.. [Word,X].

lex(whpr((X^P)^X^and(person(X),P)),who).
lex(whpr((X^P)^X^and(thing(X),P)),what).
lex(n(X^bus(X)),bus).
lex(aux([]),did).
lex(aux([]),does).
lex(rel([]),that).

lex(n(X^weapon(X)),weapon).
lex(n(X^passenger(X)),passenger).
lex(n(X^man(X)),man).

lex(p((Y^in(X,Y))^Q^(X^P)^and(P,Q)),in).
lex(p((Y^on(X,Y))^Q^(X^P)^and(P,Q)),on).


lex(adj((X^P)^X^and(P,big(X))),yellow).
% lex(adj((X^P)^X^and(P,big(X))),blue).
lex(adj((X^P)^X^and(P,old(X))),old).
lex(adj((X^P)^X^and(P,illegal(X))),illegal).

lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),a).
lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),an).
lex(dt((X^P)^(X^Q)^the(X,(and(P,Q)))),the).
lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),some).
lex(dt((X^P)^(X^Q)^forall(X,(imp(P,Q)))),each).
lex(dt((X^P)^(X^Q)^forall(X,(imp(P,Q)))),every).


lex(iv(X^sneezed(X)),sneezed).
lex(tv(X^Y^saw(X,Y)),saw).
lex(tv(X^Y^have(X,Y)),has).



lex(tv((X^Y^Z),[]),Word):-name(Word,Word1),prefix(W,Word1),name(W1,W),lemma(W1,tv),Z =.. [W1,X,Y].


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

srparse(Stack,SentenceRepr,[Word|Words]):-
        lex(X,Word),
        srparse([X|Stack],SentenceRepr,Words).


