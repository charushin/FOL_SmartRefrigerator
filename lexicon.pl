% ==================================
% Lexicon
% ==================================
% = tv(_G294^_G297^contain(_G294,_G297),[ ])
lex(pn((tom^X)^X),tom).
lex(pn((sue^X)^X),sue).

lex(n(X^P),Word):- lemma(Word,n), P =.. [Word,X].
lex(pn((Word^X)^X),Word):-lemma(Word,pn).
lex(adj((X^P)^X^and(P,Z)),Word):-lemma(Word,adj), Z =.. [Word,X].
lex(tv((X^Y)^Z),Word):-lemma(Word,tv),Z =.. [Word,X,Y].

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
lex(adj((X^P)^X^and(P,big(X))),blue).
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



%lex(tv(X^Y^contain(X,Y)),contains).
lex(tv(X^Y^Z),Word):-name(Word,Word1),prefix(W,Word1),name(W1,W),lemma(W1,tv),Z =.. [W1,X,Y].
%lex(tv(X^Y^contain(X,Y)),contained).