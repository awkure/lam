#!/usr/bin/env python3

import copy
from typing import TypeVar, Callable, List, Sequence, Dict, Union

A = TypeVar('A')
B = TypeVar('B')
C = TypeVar('C')


def compose (g : Callable[[B],C], f : Callable[[A],B]) -> Callable[[A],C]:
    def _h (*args : Sequence[A], **kwargs : Dict[str, A]) -> C:
        return g(f(*args, **kwargs))
    return _h


def curry (f : Callable[[A],B]) -> Callable[[B],C]:
    _args   = []
    _kwargs = {}

    def _h (*args : Sequence[B], **kwargs : Dict[str, B]) -> C:
        nonlocal _args, _kwargs
        if args or kwargs:
            _args += args 
            _kwargs.update(kwargs)
            return _h
        else:
            return f(*_args, *_kwargs)
    
    return _h


def fix (f : Callable[[A],A]) -> A:
    return (lambda x : x(x)) (lambda y : f(lambda *args : y(y)(*args)))


class Var (object):
    def __init__ (self, name : str):
        self._name = name 

    def __call__ (self):
        return self

    def __str__ (self) -> str:
        return str (self._name)

    def __eq__ (self, other) -> bool:
        if isinstance (other, Var):
            if other._name == self._name:
                return True 
        return False 

    def iswhnf (self) -> bool:
        return True 

    @property
    def name (self) -> str:
        return self._name

    @name.setter
    def name (self, name : str):
        self._name = name


class Lam (object):
    def __init__ (self, var : str, body):
        self._var  = var 
        self._body = body

    def __call__ (self, body):
        beta_reduce(App (self, body))

    def __str__ (self) -> str:
        return 'λ' + str (self._var) + '.' + str (self._body)

    def __eq__ (self, other) -> bool:
        if isinstance (other, Lam):
            return (other._var == self._var) and (other._body == self._body)
        return False 

    def iswhnf (self) -> bool:
        return True

    @property
    def var (self) -> str:
        return self._var 

    @property
    def body (self):
        return self._body


class App (object):
    def __init__ (self, lhs, rhs):
        self._rhs = rhs
        self._lhs = lhs 

    def __call__ (self):
        beta_reduce(self)

    def __str__ (self) -> str:
        return str (self._lhs) + str (self._rhs)

    def __eq__ (self, other) -> bool:
        if isinstance (other, App):
            return (other._lhs == self._lhs) and (other._rhs == self._rhs)
        return False 

    def iswhnf (self) -> bool:
        if isinstance (self._lhs, Lam):
            return False 
            
        elif isinstance (self._lhs, App):
            return self._lhs.iswhnf()
        
        else:
            return True 


def bound_vars (term) -> Union:
    if isinstance(term, Var):
        return set([])

    elif isinstance(term, App):
        return compose(bound_vars(term._lhs).union, bound_vars)(term._rhs)

    elif isinstance(term, Lam):
        return compose(set([term._var]).union, bound_vars)(term._body)


def free_vars (term) -> Union:
    if isinstance(term, Var):
        return set([term._name])

    elif isinstance(term, App):
        return compose(free_vars(term._lhs).union, free_vars)(term._rhs)

    elif isinstance(term, Lam):
        return free_vars(term._body).difference(term._var)


def subst (term, next, next_):
    if isinstance(term, Var):
        if term._name == next._name:
            return copy.deepcopy(next_)
        
    elif isinstance(term, App):
        term._lhs = subst(term._lhs, next, next_)
        term._rhs = subst(term._rhs, next, next_)

    elif isinstance(term, Lam):
        if term._var == next: term._var = subst(term._var, next, next_)
        term._body = subst(term._body, next, next_)

    return copy.deepcopy (term)


def beta_reduce (term):
    if isinstance(term, Var):
        return term

    elif isinstance(term, Lam):
        return term

    elif isinstance(term, App):
        if isinstance(term._lhs, Lam):
            return subst(term._lhs._body, term._lhs._var, term._rhs)

        else:
            _lhs = beta_reduce(term._lhs)

            if _lhs != term._lhs:
                term._lhs = _lhs
                return term
            
            else:
                term._rhs = beta_reduce(term._rhs)
                return term

_true  = Lam ('a', Lam ('b', Var ('b')))
_false = Lam ('a', Lam ('b', Var ('a')))
_and   = Lam ('a', Lam ('b', App (App (Var ('b'), Var('a')), _false)))
_or    = Lam ('a', Lam ('b', App (App (Var ('b'), _true), (Var ('a')))))
_not   = Lam ('a', App (App (Var ('a'), _false), _true))

if __name__ == "__main__":
    t = compose(_not, _not)(_true)
    compose(print, fix(beta_reduce))(t)