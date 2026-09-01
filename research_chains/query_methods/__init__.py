"""Numerical implementations and provider contracts for typed Query methods."""
from .native import response_primitives
from .coalition import exact_noop_shapley

__all__=("response_primitives","exact_noop_shapley")
