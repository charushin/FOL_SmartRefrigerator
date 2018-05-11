rule(s(Y),[np(X^Y),vp(X)]).                

rule(vp(X^W),[tv(X^Y),np(Y^W)]).
rule(vp(X),[iv(X)]).

%Verbal rules
rule(vp(X^K,[]),[tv(X^Y,[]),np(Y^K)]).
rule(vp(X,WH),[iv(X,WH)]).
rule(s(Y,WH),[np(X^Y),vp(X,WH)]).

rule(vp(K,[WH]),[tv(Y,[WH]),np(Y^K)]).
rule(s(X,[WH]),[vp(X,[WH])]).


rule(np(Y),[dt(X^Y),n(X)]).
rule(np(X),[pn(X)]).

rule(n(Y),[adj(X^Y),n(X)]).

rule(n(X^Z),[n(X^Y),pp((X^Y)^Z)]).
rule(pp(Z),[p(X^Y^Z),np(X^Y)]).

rule(vp(X^W^Z),[dtv(X^Y^Y1),np(Y^W),np(Y1^Z)]).
rule(vp(X^W),[vp(X^Y),pp(Y^W)]).
rule(vp(X^W),[sv(X^Y),s(Y^W)]).
rule(np(X),[prp(X)]).


rule(q(Y),[whpr(X^Y),vp(X)]).
rule(q(X),[whpr(X^Y),aux([]),vp(Y)]).

%rule(q(Z),[whpr((X^Y)^Z),inv_s(Y,[X])]).

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