:- use_module(library(assoc)).
:- use_module(library(coinduction)).
:- coinductive substitution_aux/3.
:- coinductive filter_events/4.
:- coinductive are_all_events_atomic/2.
:- coinductive are_all_events_async/2.
:- dynamic message_list/1, str/1, attrType/3, agents/1.

%debug(on).

/*******************************************************************************************/
/*                              PARAMETRIC TRACE EXPRESSIONS                               */
/*******************************************************************************************/

/* Transition rules */

% next transition function (parametric version)
next(ProtocolName, ET:T, E, T, S) :-
  genvar(ET, ETFree, S1),
  match(ProtocolName, E, ETFree),
  clear(S1, S).
next(ProtocolName, T1\/_, E, T2, S) :-
  next(ProtocolName, T1, E, T2, S).
next(ProtocolName, _\/T1, E, T2, S) :-
  !, next(ProtocolName, T1, E, T2, S).
next(ProtocolName, T1|T2, E, T, S) :-
  next(ProtocolName, T1, E, T3, S),
  fork(T3, T2, T).
next(ProtocolName, T1|T2, E, T, S) :-
    !, next(ProtocolName, T2, E, T3, S),
  fork(T1, T3, T).
next(ProtocolName, T1*T2, E, T, S) :-
  next(ProtocolName, T1, E, T3, S),
  concat(T3, T2, T).
next(ProtocolName, T1*T2, E, T3, S) :-
  !, may_halt(T1),
  next(ProtocolName, T2, E, T3, S).
next(ProtocolName, T1/\T2, E, T, S) :-
  !, next(ProtocolName, T1, E, T3, S1),
  next(ProtocolName, T2, E, T4, S2),
  merge(S1, S2, S),
  conj(T3, T4, T).
next(ProtocolName, ET>>T, E, ET>>T1, S) :-
  event(ProtocolName, E),
  genvar(ET, ETFree, S1),
  (match(ProtocolName, E, ETFree) *->
    (clear(S1, S2),
     next(ProtocolName, T, E, T1, S3),
     merge(S2, S3, S));
     (T=T1, S = [])).
next(ProtocolName, var(X, T), E, T2, S) :-
  next(ProtocolName, T, E, T1, S1),
  (syntactic_member_couples((X=V), S1) ->
    (substitution(T1, (X=V), T2),% !,
     remove((X=V), S1, S));
    (T2 = var(X, T1), S = S1)).
% (main)
next(ProtocolName, T, E, T1) :-
  next(ProtocolName, T, E, T1, S), S = [].


may_halt(epsilon) :- !.
may_halt(T1\/T2) :- (may_halt(T1), !; may_halt(T2)).
may_halt(T1|T2) :- !, may_halt(T1), may_halt(T2).
may_halt(T1*T2) :- !, may_halt(T1), may_halt(T2).
may_halt(T1/\T2) :- !, may_halt(T1), may_halt(T2).
may_halt(_>>T) :- !, may_halt(T).
may_halt(var(_, T)) :- !, may_halt(T).

does_not_halt(_:_).
does_not_halt(T1\/T2) :- !, does_not_halt(T1), does_not_halt(T2).
does_not_halt(T1|T2) :- (does_not_halt(T1), !; does_not_halt(T2)).
does_not_halt(T1*T2) :- (does_not_halt(T1), !; does_not_halt(T2)).
does_not_halt(T1/\T2) :- (does_not_halt(T1), !; does_not_halt(T2)).
does_not_halt(_>>T) :- !, does_not_halt(T).
does_not_halt(var(_, T)) :- !, does_not_halt(T).

% may_halt predicate iterated on the trace expression
% Example: T = msg1:epsilon, may_eventually_halt(T).
% Example: T = msg1:T, not(may_eventually_halt(T)).
may_eventually_halt(ProtocolName, T) :-
  empty_assoc(A),
  may_eventually_halt(ProtocolName, T, A).
may_eventually_halt(_, T, A) :-
  get_assoc(T, A, _), !, fail.
may_eventually_halt(_, T, _) :- may_halt(T), !.
may_eventually_halt(ProtocolName, T, A) :-
  put_assoc(T, A, _, A1),
  next(ProtocolName, T, _, T1), may_eventually_halt(ProtocolName, T1, A1).

%%% optimization
fork(epsilon, T, T) :- !.
fork(T, epsilon, T) :- !.
fork((T1l|T1r), T2, (T1l|(T1r|T2))) :- !.
fork(T1, T2, (T1|T2)).

concat(epsilon, T, T) :- !.
concat(T, epsilon, T) :- !.
concat((T1l*T1r), T2, T1l*(T1r*T2)) :- !.
concat(T1, T2, T1*T2).

conj(epsilon/\epsilon, epsilon) :- !.
conj((T1l/\T1r), T2, T1l/\(T1r/\T2)) :- !.
conj(T1, T2, T1/\T2).

% Predicate which takes an event type and a variable ('$VAR'(N)) returning
% a new event type where all '$VAR'(N) are substituted with free variables
% and a list of substitutions recording the association between each ground
% variables with the new free variables.
% Example: genvar(ping('$VAR'(0)), ping(X), ['$VAR'(0)=X], '$VAR'(0))
% Example: genvar(ping('$VAR'(1)), ping('$VAR'(1)), [], '$VAR'(0))
genvar(ET, ETFree, [(X=V)], X) :-
  genvar(ET, ETFree, [(X=V)]), !.
genvar(ET, ET, [], _).

% Predicate which takes an event type returning a new event type where
% all '$VAR'(_) are substituted with free variables and a list of substitutions recording the association between each ground
% variables with the new free variables.
% Example: genvar(ping('$VAR'(0)), ping(X), ['$VAR'(0)=X])
% Example: genvar(ping('$VAR'(1)), ping(X), ['$VAR'(1)=X])
% Example: genvar(pong('$VAR'(0), '$VAR'(1)), pong(X, Y), ['$VAR'(0)=X, '$VAR'(1)=Y])
genvar(ET, ETFree, S) :-
  functor(ET, F, N),
  (N == 0 -> (ETFree = ET, S = []);
  (findall(Arg, arg(_, ET, Arg), Args),
  functor(ETFree, F, N),
  genvar_aux(Args, ETFree, 1, S))).
genvar_aux([], _, _, []).
genvar_aux([H1|T1], ETFree, N, [(H1=Arg)|S]) :-
  functor(H1, '$VAR', _), !,
  arg(N, ETFree, Arg),
  N1 is N+1,
  genvar_aux(T1, ETFree, N1, S).
genvar_aux([H1|T1], ETFree, N, S) :-
  arg(N, ETFree, Arg),
  H1 = Arg,
  N1 is N+1,
  genvar_aux(T1, ETFree, N1, S).

% Substitution function -
% It is used to substitute a variable inside an event types
% Example: substitution(ping('$VAR'(0)):epsilon, ('$VAR'(0)=a), ping(a):epsilon)
substitution(T, S, T1) :-
  substitution_aux(T, S, T1), !.
substitution_aux(epsilon, _, epsilon).
substitution_aux(ET:T, (X=V), ET1:T1) :-
  genvar(ET, ET1, S, X),
  ((member((X=V), S), !);true),
  substitution_aux(T, (X=V), T1).
substitution_aux(T1\/T2, S, T3\/T4) :-
  substitution_aux(T1, S, T3),
  substitution_aux(T2, S, T4).
substitution_aux(T1|T2, S, T3|T4) :-
  substitution_aux(T1, S, T3),
  substitution_aux(T2, S, T4).
substitution_aux(T1*T2, S, T3*T4) :-
  substitution_aux(T1, S, T3),
  substitution_aux(T2, S, T4).
substitution_aux(T1/\T2, S, T3/\T4) :-
  substitution_aux(T1, S, T3),
  substitution_aux(T2, S, T4).
substitution_aux(ET>>T, (X=V), ET1>>T1) :-
  genvar(ET, ET1, S, X),
  ((member((X=V), S), !);true),
  substitution_aux(T, (X=V), T1).
substitution_aux(var(X, T), (X=_), var(X, T)) :- !.
substitution_aux(var(X, T), S, var(X, T1)) :-
  substitution_aux(T, S, T1).

% Member function with syntactic equality (on couples)
% Example: syntactic_member_couples((X=a), [(Y=a), (Z=b), (X=a)]) -> true
% Example: syntactic_member_couples((X=a), [(Y=a), (Z=b)]) -> false
syntactic_member_couples((E=V), [(H=V)|_]) :-
  E == H, !.
syntactic_member_couples(E, [_|T]) :-
  syntactic_member_couples(E, T).

% Member function with syntactic equality (on singleton)
syntactic_member(E, [H|_]) :-
  E == H, !.
syntactic_member(E, [_|T]) :-
  syntactic_member(E, T).

% Add a new substitution to the substitution set
% Example: add((X=a), [X=a], [X=a]).
% Example: add((X=a), [], [X=a]).
% Example: add((X=a), [X=b], _) -> false
add(E, [], [E]).
add((E=X), [(H=V)|T], [(H=V)|T1]) :-
  E \== H, !,
  add((E=X), T, T1).
add((_=V), [(H=V)|T], [(H=V)|T]).

% Remove a substitution from the substitution set
% Example: remove((X=a), [X=a], []).
% Example: remove((X=a), [], []).
% Example: remove((X=a), [X=b], _) -> false
remove(_, [], []).
remove((E=X), [(H=V)|T], [(H=V)|T1]) :-
  E \== H, !,
  remove((E=X), T, T1).
remove((E=V), [(_=V)|T], T1) :-
  remove((E=V), T, T1).

% Merge two substitution sets
% Example: merge([(X=a)], [(Y=b)], [Y=b, X=a])
% Example: merge([(X=a)], [(X=a)], [X=a])
% Example: merge([(X=a)], [(X=b)], _) -> false
merge([], L, L).
merge([H|T], L, L2) :-
  add(H, L, L1),
  merge(T, L1, L2), !.

% Remove from a substitution set all couples (_=_)
% Example: clear([(X=a), (Y=b)], [(X=a), (Y=b)])
% Example: clear([(X=a), (Y=_)], [(X=a)])
clear([], []).
clear([(_=Y)|T], T1) :-
  var(Y), !, clear(T, T1).
clear([H|T], [H|T1]) :-
  clear(T, T1).


accept(T, []) :-
  may_halt(T).
accept(T1, [E|L]) :-
  next(_, T1, E, T2), accept(T2, L).

accept(_, T, [*]) :-
  may_halt(T).
accept(0, T, []) :-
  !, does_not_halt(T).
accept(N, T1, [E|L]) :-
  !, next(_, T1, E, T2),
  M is N - 1,
  accept(M, T2, L).

% one more argument: the residual term
accept(_,T,[*],T) :-
  may_halt(T).
accept(0,T,[],T) :-
  !,does_not_halt(T).
accept(N,T1,[E|L],T3) :-
  !, next(_, T1,E,T2),
  M is N - 1,
  accept(M,T2,L,T3).

is_contractive_aux(ProtocolName) :-
  trace_expression(ProtocolName, T),
  threshold(Threshold),
  filter_events(T, TFiltered, Threshold, ProtocolName),
  is_contractive(TFiltered).

is_contractive(T) :-
  empty_assoc(A),
  is_contractive(T, 0, -1, A).

is_contractive(epsilon, _, _, _) :- !.
is_contractive(T, _Depth, DeepestSeq, Assoc) :-
  get_assoc(T, Assoc, LoopDepth), !,
  LoopDepth =< DeepestSeq.
is_contractive(ET:T, Depth, _DeepestSeq, Assoc) :-
  put_assoc(ET:T, Assoc, Depth, Assoc1),
  IncDepth is Depth + 1,
  is_contractive(T, IncDepth, Depth, Assoc1).
is_contractive(T1\/T2, Depth, DeepestSeq, Assoc) :-
  put_assoc(T1\/T2, Assoc, Depth, Assoc1),
  IncDepth is Depth + 1,
  is_contractive(T1, IncDepth, DeepestSeq, Assoc1),
  is_contractive(T2, IncDepth, DeepestSeq, Assoc1).
is_contractive(T1|T2, Depth, DeepestSeq, Assoc) :-
  put_assoc(T1|T2, Assoc, Depth, Assoc1),
  IncDepth is Depth + 1,
  is_contractive(T1, IncDepth, DeepestSeq, Assoc1),
  is_contractive(T2, IncDepth, DeepestSeq, Assoc1).
is_contractive(T1*T2, Depth, DeepestSeq, Assoc) :-
  put_assoc(T1*T2, Assoc, Depth, Assoc1),
  IncDepth is Depth + 1,
  is_contractive(T1, IncDepth, DeepestSeq, Assoc1),
  ((may_halt(T1)) ->
    (is_contractive(T2, IncDepth, DeepestSeq, Assoc1));
    (is_contractive(T2, IncDepth, Depth, Assoc1))).
is_contractive(T1/\T2, Depth, DeepestSeq, Assoc) :-
  put_assoc(T1/\T2, Assoc, Depth, Assoc1),
  IncDepth is Depth + 1,
  is_contractive(T1, IncDepth, DeepestSeq, Assoc1),
  is_contractive(T2, IncDepth, DeepestSeq, Assoc1).
is_contractive(ET>>T, Depth, DeepestSeq, Assoc) :-
  put_assoc(ET>>T, Assoc, Depth, Assoc1),
  IncDepth is Depth + 1,
  is_contractive(T, IncDepth, DeepestSeq, Assoc1).
is_contractive(var(X, T), Depth, DeepestSeq, Assoc) :-
  put_assoc(var(X, T), Assoc, _, Assoc1),
  IncDepth is Depth + 1,
  is_contractive(T, IncDepth, DeepestSeq, Assoc1).

% filter_events(T, TFiltered, Threshold, ProtocolName) :-
%   empty_assoc(A),
%   filter_events(T, TFiltered, A, Threshold, ProtocolName).
%
% filter_events(epsilon, epsilon, _, _, _) :- !.
% filter_events(T, TFiltered, Assoc, _, _) :-
%   get_assoc(T, Assoc, TFiltered), !.
% filter_events(ET:T, TFiltered, Assoc, Threshold, ProtocolName) :-
%   reliable(ProtocolName, ET, 0), !,
%   put_assoc(ET:T, Assoc, TFiltered, Assoc1),
%   filter_events(T, TFiltered, Assoc1, Threshold, ProtocolName).
% filter_events(ET:T, TFiltered, Assoc, Threshold, ProtocolName) :-
%   reliable(ProtocolName, ET, 1), !,
%   put_assoc(ET:T, Assoc, TFiltered, Assoc1),
%   filter_events(T, T1, Assoc1, Threshold, ProtocolName),
%   TFiltered = ET:T1.
% filter_events(ET:T, TFiltered, Assoc, Threshold, ProtocolName) :-
%   reliable(ProtocolName, ET, Perc),
%   put_assoc(ET:T, Assoc, TFiltered, Assoc1),
%   filter_events(T, T1, Assoc1, Threshold, ProtocolName),
%   ((Perc =< Threshold) ->
%     (TFiltered = ((ET:epsilon) \/ epsilon) * T1);
%     (TFiltered = ET:T1)).
% filter_events(T1\/T2, TFiltered, Assoc, Threshold, ProtocolName) :-
%   put_assoc(T1\/T2, Assoc, TFiltered, Assoc1),
%   filter_events(T1, TFiltered1, Assoc1, Threshold, ProtocolName),
%   filter_events(T2, TFiltered2, Assoc1, Threshold, ProtocolName),
%   TFiltered = TFiltered1 \/ TFiltered2.
% filter_events(T1|T2, TFiltered, Assoc, Threshold, ProtocolName) :-
%   put_assoc(T1|T2, Assoc, TFiltered, Assoc1),
%   filter_events(T1, TFiltered1, Assoc1, Threshold, ProtocolName),
%   filter_events(T2, TFiltered2, Assoc1, Threshold, ProtocolName),
%   fork(TFiltered1, TFiltered2, TFiltered).
% filter_events(T1*T2, TFiltered, Assoc, Threshold, ProtocolName) :-
%   put_assoc(T1*T2, Assoc, TFiltered, Assoc1),
%   filter_events(T1, TFiltered1, Assoc1, Threshold, ProtocolName),
%   filter_events(T2, TFiltered2, Assoc1, Threshold, ProtocolName),
%   concat(TFiltered1, TFiltered2, TFiltered).
% filter_events(T1/\T2, TFiltered, Assoc, Threshold, ProtocolName) :-
%   put_assoc(T1/\T2, Assoc, TFiltered, Assoc1),
%   filter_events(T1, TFiltered1, Assoc1, Threshold, ProtocolName),
%   filter_events(T2, TFiltered2, Assoc1, Threshold, ProtocolName),
%   conj(TFiltered1, TFiltered2, TFiltered).
% filter_events(ET>>T, TFiltered, Assoc, Threshold, ProtocolName) :-
%   put_assoc(ET>>T, Assoc, TFiltered, Assoc1),
%   filter_events(T, T1, Assoc1, Threshold, ProtocolName),
%   TFiltered = (ET>>T1).

% filter events inside the trace expression generating a new one where:
% - all event types ET with reliable(ProtocolName, ET, 0) are removed by the trace expression
% - all event types ET with reliable(ProtocolName, ET, Perc) and Perc > Threshold are preserved
% - all event types ET with reliable(ProtocolName, ET, Perc) and Perc <= Threshold become optional
%   ET:T ---optional---> ((ET:epsilon)\/epsilon)*T
filter_events(epsilon, epsilon, _, _) :- !.
filter_events(ET:T, TFiltered, Threshold, ProtocolName) :-
  reliable(ProtocolName, ET, 0), !,
  filter_events(T, TFiltered, Threshold, ProtocolName).
filter_events(ET:T, TFiltered, Threshold, ProtocolName) :-
  reliable(ProtocolName, ET, 1), !,
  filter_events(T, T1, Threshold, ProtocolName),
  TFiltered = ET:T1, !.
filter_events(ET:T, TFiltered, Threshold, ProtocolName) :-
  reliable(ProtocolName, ET, Perc),
  filter_events(T, T1, Threshold, ProtocolName),
  ((Perc =< Threshold) ->
    (TFiltered = ((ET:epsilon) \/ epsilon) * T1);
    (TFiltered = ET:T1)), !.
filter_events(T1\/T2, TFiltered, Threshold, ProtocolName) :-
  filter_events(T1, TFiltered1, Threshold, ProtocolName),
  filter_events(T2, TFiltered2, Threshold, ProtocolName),
  TFiltered = (TFiltered1 \/ TFiltered2), !.
filter_events(T1|T2, TFiltered1|TFiltered2, Threshold, ProtocolName) :-
  filter_events(T1, TFiltered1, Threshold, ProtocolName),
  filter_events(T2, TFiltered2, Threshold, ProtocolName), !.
  %fork(TFiltered1, TFiltered2, TFiltered), !.
filter_events(T1*T2, TFiltered1*TFiltered2, Threshold, ProtocolName) :-
  filter_events(T1, TFiltered1, Threshold, ProtocolName),
  filter_events(T2, TFiltered2, Threshold, ProtocolName), !.
  %concat(TFiltered1, TFiltered2, TFiltered), !.
filter_events(T1/\T2, TFiltered1/\TFiltered2, Threshold, ProtocolName) :-
  filter_events(T1, TFiltered1, Threshold, ProtocolName),
  filter_events(T2, TFiltered2, Threshold, ProtocolName), !.
  %conj(TFiltered1, TFiltered2, TFiltered), !.
filter_events(ET>>T, TFiltered, Threshold, ProtocolName) :-
  filter_events(T, TFiltered1, Threshold, ProtocolName),
  TFiltered = (ET>>TFiltered1), !.
filter_events(var(X, T), TFiltered, Threshold, ProtocolName) :-
  filter_events(T, TFiltered1, Threshold, ProtocolName),
  TFiltered = var(X, TFiltered1), !.

are_all_events_atomic(ProtocolName) :-
  trace_expression(ProtocolName, T),
  are_all_events_atomic(T, ProtocolName).

% are_all_events_atomic(T) :-
%   empty_assoc(A),
%   are_all_events_atomic(T, A), !.
%
% are_all_events_atomic(epsilon, _).
% are_all_events_atomic(T, Assoc) :-
%   get_assoc(T, Assoc, _), !.
% are_all_events_atomic(ET:T, Assoc) :-
%   put_assoc(ET:T, Assoc, _, Assoc1),
%   term_string(ET, S),
%   split_string(S, "_", "", L),
%   not(last(L, "s")),
%   not(last(L, "r")),
%   are_all_events_atomic(T, Assoc1).
% are_all_events_atomic(T, Assoc) :-
%   (T = (T1\/T2); T = (T1|T2); T = (T1*T2); T = (T1/\T2)), !,
%   put_assoc(T, Assoc, _, Assoc1),
%   are_all_events_atomic(T1, Assoc1),
%   are_all_events_atomic(T2, Assoc1).
% are_all_events_atomic(ET>>T, Assoc) :-
%   put_assoc(ET>>T, Assoc, _, Assoc1),
%   term_string(ET, S),
%   split_string(S, "_", "", L),
%   not(last(L, "s")),
%   not(last(L, "r")),
%   are_all_events_atomic(T, Assoc1).

are_all_events_atomic(epsilon, _).
are_all_events_atomic(ET:T, ProtocolName) :-
  findall(E, (match(ProtocolName, E, ET), E = msg(_, _, _, _, Type, _), (Type == s; Type == r)), []),
  are_all_events_atomic(T, ProtocolName), !.
  % term_string(ET, S),
  % split_string(S, "_", "", L),
  % not(last(L, "s")),
  % not(last(L, "r")),
  % are_all_events_atomic(T), !.
are_all_events_atomic(T, ProtocolName) :-
  (T = (T1\/T2); T = (T1|T2); T = (T1*T2); T = (T1/\T2)), !,
  are_all_events_atomic(T1, ProtocolName),
  are_all_events_atomic(T2, ProtocolName), !.
are_all_events_atomic(ET>>T, ProtocolName) :-
  findall(E, (match(ProtocolName, E, ET), E = msg(_, _, _, _, Type, _), (Type == s; Type == r)), []),
  are_all_events_atomic(T, ProtocolName), !.
  % term_string(ET, S),
  % split_string(S, "_", "", L),
  % not(last(L, "s")),
  % not(last(L, "r")),
  % are_all_events_atomic(T, ProtocolName), !.
are_all_events_atomic(var(_, T), ProtocolName) :-
  are_all_events_atomic(T, ProtocolName), !.

are_all_events_async(ProtocolName) :-
  trace_expression(ProtocolName, T),
  are_all_events_async(T, ProtocolName).

are_all_events_async(epsilon, _).
are_all_events_async(ET:T, ProtocolName) :-
  findall(E, (match(ProtocolName, E, ET), E = msg(_, _, _, _, Type, _), var(Type)), []),
  are_all_events_async(T, ProtocolName), !.
  % term_string(ET, S),
  % split_string(S, "_", "", L),
  % (last(L, "s");last(L, "r")),
  % are_all_events_async(T), !.
are_all_events_async(T, ProtocolName) :-
  (T = (T1\/T2); T = (T1|T2); T = (T1*T2); T = (T1/\T2)), !,
  are_all_events_async(T1, ProtocolName),
  are_all_events_async(T2, ProtocolName), !.
are_all_events_async(ET>>T, ProtocolName) :-
  findall(E, (match(ProtocolName, E, ET), E = msg(_, _, _, _, Type, _), var(Type)), []),
  are_all_events_async(T, ProtocolName), !.
  % term_string(ET, S),
  % split_string(S, "_", "", L),
  % (last(L, "s");last(L, "r")),
  % are_all_events_async(T), !.
are_all_events_async(var(_, T), ProtocolName) :-
  are_all_events_async(T, ProtocolName), !.


% are_all_events_async(T) :-
%   empty_assoc(A),
%   are_all_events_async(T, A), !.
%
% are_all_events_async(epsilon, _).
% are_all_events_async(T, Assoc) :-
%   get_assoc(T, Assoc, _), !.
% are_all_events_async(ET:T, Assoc) :-
%   put_assoc(ET:T, Assoc, _, Assoc1),
%   term_string(ET, S),
%   split_string(S, "_", "", L),
%   (last(L, "s");last(L, "r")),
%   are_all_events_async(T, Assoc1).
% are_all_events_async(T, Assoc) :-
%   (T = (T1\/T2); T = (T1|T2); T = (T1*T2); T = (T1/\T2)), !,
%   put_assoc(T, Assoc, _, Assoc1),
%   are_all_events_async(T1, Assoc1),
%   are_all_events_async(T2, Assoc1).
% are_all_events_async(ET>>T, Assoc) :-
%   put_assoc(ET>>T, Assoc, _, Assoc1),
%   term_string(ET, S),
%   split_string(S, "_", "", L),
%   (last(L, "s");last(L, "r")),
%   are_all_events_async(T, Assoc1).



/* ************************************************************************** */
/* 							DYNAMIC PROJECTION				 			      */
/* ************************************************************************** */

project(ProtocolName, T, ProjectedAgents, ProjectedType) :-
	empty_assoc(A),
	project(ProtocolName, A, 0, -1, T, ProjectedAgents, ProjectedType).

project(_, _Assoc, _Depth, _DeepestSeq, epsilon, _ProjectedAgents, epsilon):- !.

project(_, Assoc, _Depth, DeepestSeq, Type, _ProjectedAgents, ProjectedType) :-
get_assoc(Type,Assoc,(AssocProjType,LoopDepth)),!,(LoopDepth =< DeepestSeq -> ProjectedType=AssocProjType; ProjectedType=epsilon).
/*
project(Assoc, Depth, DeepestSeq, (IntType:Type1), ProjectedAgents, ProjectedType) :-
IntType \= (_, _),
!,
put_assoc((IntType:Type1),Assoc,(ProjectedType,Depth),NewAssoc),
(involves(IntType, ProjectedAgents) ->
    IncDepth is Depth+1,project(NewAssoc,IncDepth,Depth,Type1,ProjectedAgents,ProjectedType1),ProjectedType=(IntType:ProjectedType1);
    project(NewAssoc,Depth,DeepestSeq,Type1,ProjectedAgents,ProjectedType)).
*/
project(ProtocolName, Assoc, Depth, DeepestSeq, (IntType:Type1), ProjectedAgents, ProjectedType) :-
!,
put_assoc((IntType:Type1),Assoc,(ProjectedType,Depth),NewAssoc),
(involves(ProtocolName, IntType, ProjectedAgents) ->
    IncDepth is Depth+1,project(ProtocolName, NewAssoc,IncDepth,Depth,Type1,ProjectedAgents,ProjectedType1),ProjectedType=(IntType:ProjectedType1);
    project(ProtocolName, NewAssoc,Depth,DeepestSeq,Type1,ProjectedAgents,ProjectedType)).

project(ProtocolName, Assoc, Depth, DeepestSeq, (Type1|Type2), ProjectedAgents, ProjectedType) :-
!,
put_assoc((Type1|Type2),Assoc,(ProjectedType,Depth),NewAssoc),
IncDepth is Depth+1,
project(ProtocolName, NewAssoc, IncDepth, DeepestSeq, Type1, ProjectedAgents, ProjectedType1),
project(ProtocolName, NewAssoc, IncDepth, DeepestSeq, Type2, ProjectedAgents, ProjectedType2),
ProjectedType=(ProjectedType1|ProjectedType2).

project(ProtocolName, Assoc, Depth, DeepestSeq, (Type1\/Type2), ProjectedAgents, ProjectedType) :-
!,
put_assoc((Type1\/Type2),Assoc,(ProjectedType,Depth),NewAssoc),
IncDepth is Depth+1,
project(ProtocolName, NewAssoc, IncDepth, DeepestSeq, Type1, ProjectedAgents, ProjectedType1),
project(ProtocolName, NewAssoc, IncDepth, DeepestSeq, Type2, ProjectedAgents, ProjectedType2),
ProjectedType=(ProjectedType1\/ProjectedType2).

project(ProtocolName, Assoc, Depth, DeepestSeq, (Type1/\Type2), ProjectedAgents, ProjectedType) :-
!,
put_assoc((Type1/\Type2),Assoc,(ProjectedType,Depth),NewAssoc),
IncDepth is Depth+1,
project(ProtocolName, NewAssoc, IncDepth, DeepestSeq, Type1, ProjectedAgents, ProjectedType1),
project(ProtocolName, NewAssoc, IncDepth, DeepestSeq, Type2, ProjectedAgents, ProjectedType2),
ProjectedType=(ProjectedType1/\ProjectedType2).

project(ProtocolName, Assoc, Depth, DeepestSeq, (Type1*Type2), ProjectedAgents, ProjectedType) :-
!,
put_assoc((Type1*Type2),Assoc,(ProjectedType,Depth),NewAssoc),
IncDepth is Depth+1,
project(ProtocolName, NewAssoc, IncDepth, DeepestSeq, Type1, ProjectedAgents, ProjectedType1),
((may_halt(Type1))->
  (project(ProtocolName, NewAssoc, IncDepth, DeepestSeq, Type2, ProjectedAgents, ProjectedType2));
  (project(ProtocolName, NewAssoc, IncDepth, Depth, Type2, ProjectedAgents, ProjectedType2))),
ProjectedType=(ProjectedType1*ProjectedType2).

project(ProtocolName, Assoc, Depth, DeepestSeq, (IntType>>Type1), ProjectedAgents, ProjectedType) :-
!,
put_assoc((IntType>>Type1),Assoc,(ProjectedType,Depth),NewAssoc),
%(involves(IntType, ProjectedAgents) ->
IncDepth is Depth+1,
project(ProtocolName, NewAssoc,IncDepth,DeepestSeq,Type1,ProjectedAgents,ProjectedType1),ProjectedType=(IntType>>ProjectedType1).%;

project(ProtocolName, Assoc, Depth, DeepestSeq, var(X,Type1), ProjectedAgents, ProjectedType) :-
!,
put_assoc(var(X,Type1),Assoc,(ProjectedType,Depth),NewAssoc),
IncDepth is Depth + 1,
project(ProtocolName, NewAssoc, IncDepth, DeepestSeq, Type1, ProjectedAgents, ProjectedType1),
ProjectedType = var(X, ProjectedType1).

/****************************************************************************/
/* 	  INVOLVES PREDICATE: can be redefined to consider agent roles      */
/****************************************************************************/

involves(ProtocolName, IntType, List) :-
  match(ProtocolName, Message, IntType),
  Message =.. [msg, performative(_P), sender(Sender), receiver(Receiver) | _T],
  (member(Sender, List);
  member(Receiver, List)).

involves(ProtocolName, IntType, List) :-
  match(ProtocolName, Action, IntType),
  Action =.. [act, agent(A), content(_C) | _T],
  member(A, List).


/****************************************************************************/
/* 	  		PREDICATES FOR REAL MONITORING   		    */
/****************************************************************************/



initialize(LogFileName, MonitorID, Agents, ProtocolName) :-
  % The argument of diff (milliseconds after which we assume that a message is "old" enough, and no older messages will arrive after) should be the same used by the progress agent to call the "progress" goal
  recorda(MonitorID, diff(0)),
  trace_expression(ProtocolName, T),
  threshold(Threshold),
  filter_events(T, TFiltered, Threshold, ProtocolName),
  project(ProtocolName, TFiltered, Agents, ProjectedType),
  clean_and_record(MonitorID, current_state(ProtocolName, ProjectedType)),
  clean_and_record(MonitorID, message_list([])),
  open(LogFileName,append,Str),
  recorda(MonitorID, str(Str)),
  recorda(MonitorID, agents(Agents)),
  write_log(MonitorID, 'Monitoring protocol\n'), write_log(MonitorID, ProjectedType),
  write_log(MonitorID,'\n\n'), !.

remember(MonitorID, Message) :-
  Message =.. Message2List,
  last(Message2List, time-stamp(TS)),
  !,
  recorded(MonitorID, message_list(List), _),
  insert_in_order((TS, Message), List, NewList),
  clean_and_record(MonitorID, message_list(NewList)).

remember(MonitorID, Message) :-
  recorded(MonitorID, message_list(List), _),
  append(List, [(z, Message)], NewList),
  clean_and_record(MonitorID, message_list(NewList)).

verify(MonitorID, _TS) :-
  recorded(MonitorID, message_list([]), _), !,
  recorded(MonitorID, diff(Diff), _),
  write_log(MonitorID,'\n'), write_log(MonitorID,'*** NO MESSAGES EXCHANGED IN THE LAST '), write_log(MonitorID,Diff), write_log(MonitorID,' MILLISECONDS ***\n').

verify(MonitorID, TS) :-
  recorded(MonitorID, message_list(Messages), _),
  recorded(MonitorID, diff(Diff), _),
  Max_TS is TS - Diff,
  type_check_list(MonitorID, Messages, Max_TS, Remainder),
  clean_and_record(MonitorID, message_list(Remainder)).

insert_in_order((TS, Message), [], [(TS, Message)]).

insert_in_order((TS, Message), [(TSH, MessageH)|Tail], [(TS, Message)|[(TSH, MessageH)|Tail]])
:- integer(TSH), TS < TSH, !.

insert_in_order((TS, Message), [(TSH, MessageH)|Tail], [(TSH, MessageH)|OrderedList]) :-
((integer(TSH), TS >= TSH); TSH == z), insert_in_order((TS, Message), Tail, OrderedList).


type_check_aux(MonitorID, Message) :-
   recorded(MonitorID, current_state(ProtocolName, LastState), Ref),
   next(ProtocolName, LastState, Message, NewState), !,
   write_log(MonitorID,'\n'), write_log(MonitorID,'Message\n'), write_log(MonitorID,Message), write_log(MonitorID,'\nleads from state \n'), write_log(MonitorID,LastState), write_log(MonitorID,'\nto state\n'), write_log(MonitorID,NewState), write_log(MonitorID,'\n'),
   erase(Ref),
   recorda(MonitorID, current_state(ProtocolName, NewState)).

type_check_aux(MonitorID, Message) :-
recorded(MonitorID, current_state(_, LastState), Ref),
write_log(MonitorID,'\n'), write_log(MonitorID,'*** DYNAMIC TYPE-CHECKING ERROR ***\nMessage '), write_log(MonitorID,Message), write_log(MonitorID,' cannot be accepted in the current state '), write_log(MonitorID,LastState), erase(Ref), fail.

type_check_list(_, [], _Max_TS,  []).

type_check_list(MonitorID, [(z, Msg)|T], Max_TS, Remainder) :-
   !,
   type_check_aux(MonitorID, Msg),
   type_check_list(MonitorID, T, Max_TS, Remainder).

type_check_list(MonitorID, [(TS, Msg)|T], Max_TS, Remainder) :-
   TS =< Max_TS, !,
   type_check_aux(MonitorID, Msg),
   type_check_list(MonitorID, T, Max_TS, Remainder).

type_check_list(_, List, _Max_TS, List).

clean_and_record(Key, current_state(ProtocolName, InitialState)) :-
   recorded(Key, current_state(_, _), Ref), !,
   erase(Ref),
   recorda(Key, current_state(ProtocolName, InitialState)).

clean_and_record(Key, current_state(ProtocolName, InitialState)) :-
   recorda(Key, current_state(ProtocolName, InitialState)).

clean_and_record(Key, message_list(L)) :-
  recorded(Key, message_list(_), Ref), !,
  erase(Ref),
  recorda(Key, message_list(L)).

clean_and_record(Key, message_list(L)) :-
  recorda(Key, message_list(L)).

clean_and_assert(message_list([])) :-
   retract(message_list(_)), !,
   assert(message_list([])).

clean_and_assert(message_list([])) :-
   assert(message_list([])).

write_log(MonitorID, Content) :-
    recorded(MonitorID, str(Str), _), write(Str, Content), flush_output(Str), write(Content), flush_output.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Check if there exist an interval
%containing the input timestamp
exist_ts(T, [(Min, Max)| _ ]) :-
    between(Min, Max, T), !.
exist_ts(T, [_|CC]) :-
    exist_ts(T, CC).

%Match function for a given timed event
match(_, (Event, Time), (Type, Con)) :-
    of_type(Event, (Type, Con)),
    exist_ts(Time, Con).

%Check if a trace is accepted by a TTE
is_accepted(Len, T, Tr) :-
    append(Tr, [*], Tr1),
    accept(Len, T, Tr1), !.
is_accepted(Len, T, Tr) :-
    accept(Len, T, Tr).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%% Parse Function %%%%%%%

event((invia, X)) :- between(0, 50, X).
event((ricevi, X)) :- between(0, 50, X).

of_type(invia, (com_set, [(0, 10)])).
of_type(ricevi, (com_set, [(0, 10)])).
%of_type(invia, (snd_set, [(0,10),(21,30)])).
%of_type(ricevi, (rec_set, [(11, 20),(31,40)])).

of_type(chiedo, (ask_set, [(1, 5)])).
of_type(risp, (ans_set, [(6, 10)])).
of_type(any, (any, [(0, inf)])).

greater(X,Y, Z) :- Z is max(X, Y).

%%%% LEAF %%%%

%Update last event with the minimum accepted time.
%In the end the maximum of the minima is the maximum of all the minima of the events
%encountered during the descent. This value represents the minimum accepted timestamp of the
%last event.

parse((CurrE, CurrT) , [( (E, T) , epsilon/\epsilon) | Bag] , (CurrMax, E)):-
  greater(CurrT, T, CurrMax),
  of_type(E , (_, [(_, Max)])),
  Max > CurrMax.

parse((CurrE, CurrT) , [( (E, T) , epsilon) | Bag] , (CurrMax, E)):-
  greater(CurrT, T, CurrMax),
  of_type(E , (_, [(_, Max)])),
  Max > CurrMax.


%%%% BODY %%%%

%Try another branch (if the list of possible next traces is not empty)
parse((CurrE, CurrT) , [ _ | [ ((E, T), Trace) | Bag ]], NewEvent) :-
  parse((CurrE, CurrT) , [((E, T), Trace) | Bag ], NewEvent).

%Main Parse
%LastE is the unknown elements.
%(CurrE,CurrT) is the event that leads to the "state" represented by the second argument.
%The second argument is the set [(Event, Time), Trace)...] such that Event is the event that leads to Trace.
%Having two events in the call allows to check the fact that the maximum of the minima must be lower than the
%maximum of the secon event.

parse((CurrE, CurrT) , [((E, T), Trace) | _ ], LastE) :-
  %The message prints "from CurrE the next event is E"
  print_message(debug, [(CurrE, CurrT) , (E, T)]),
  greater(CurrT, T, CurrMax),
  of_type(E , (_, [(_, Max)])),
  Max > CurrMax,
  findall((Ev, NextTrace) ,next(_ , Trace, Ev, NextTrace), Bag),
  %Current Time updated with maximum of the minima
  parse((E, CurrMax) , Bag, LastE).


%%%% ROOT %%%%

%Call with a fake event

%The fake event will be surely overwritten so it will never be unified in Ev
parse(T , Ev) :-
  parse((any , 0) , [((any , 0) , T)] , Ev).


%%%% TEST %%%%

test0(Event, Time) :-
    Com = (ask_set, [(1, 5)]),
    Com1 = (ans_set, [(6, 10)]),
    T = (Com:epsilon)\/(Com1:epsilon),
    parse(T , (Event, Time)). 

test1(Event, Time) :-
    Com = (ask_set, [(1, 5)]),
    Com1 = (ans_set, [(6, 10)]),
    T = Com:Com1:Com:epsilon,
    parse(T , (Event, Time)). 

test2(Event, Time) :-
    Com = (ask_set, [(1, 5)]),
    Com1 = (ans_set, [(6, 10)]),
    T = ((Com:epsilon)\/(Com1:epsilon))\/(Com:epsilon),
    parse(T , (Event, Time)). 

%Expected 8 last events with 0 as minimum accepted time.
test3(Event, Time) :-
    Com = (com_set, [(0, 10)]),
    T = ((Com:epsilon)|(Com:epsilon)),
    parse(T , (Event, Time)).

test4(Event, Time) :-
    Com = (com_set, [(0, 10)]),
    T = ((Com:epsilon)/\(Com:epsilon)),
    parse(T , (Event, Time)).