:- use_module(library(clpfd)).



parse(Type : TExp) :-.
parse(TExp1 \/ TExp2) :-. %Se va bene TExp1
parse(TExp1 \/ TExp2) :-. %Se va bene TExp2
parse(TExp1 | TExp2) :-.

parse(TExp1 /\ TExp2) :-.
parse(TExp1 * TExp2) :-.
parse(epsilon) :-.


%% EXAMPLES %%

Com = (com_set, [(0, 10)]).
T = Com:Com:Com:epsilon.
ES = [(invia, 7), (ricevi, 8), (invia, 9)].
