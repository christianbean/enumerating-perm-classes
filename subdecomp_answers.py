"""
A demo file for Permutation Pattern 2019 pre-conference workshop for the
computational mathematics line on automatic methods in enumerating permutation
classes, given by Christian Bean. This demo allows you to implement your own
version of an algorithm for performing the substitution decompostion to classes
with finitely many simple permutatios. It uses the permuta, tilings, and
comb_spec_searcher modules from the PermutaTriangle.
https://github.com/PermutaTriangle


You will need to implement the following functions:
    - embeddings
    - simples_avoiding
    - expansion
    - factor
"""
from itertools import chain

from comb_spec_searcher import (BatchRule, CombinatorialClass,
                                CombinatorialSpecificationSearcher,
                                DecompositionRule, Rule, VerificationRule,
                                StrategyPack)
from permuta import Av, Perm
from tilings import Obstruction, Requirement, Tiling

from sympy import var
from sympy.abc import x


def embeddings(perm, cells):
    """
    Yield all possible embeddings of perm into the given cells.

    An embedding should be a tuple (or iterable) of cells.
    """
    res = [[]]
    for i, v in enumerate(perm):
        new_res = []
        for pos in res:
            last_idx = pos[-1][0] if pos else -1
            for cell in cells:
                if cell[0] < last_idx:
                    continue
                good = True
                for j, past_cell in enumerate(pos):
                    if perm[j] < perm[i]:
                        if past_cell[1] > cell[1]:
                            good = False
                            break
                    else:
                        if past_cell[1] < cell[1]:
                            good = False
                            break
                if good:
                    new_res.append(pos + [cell])
        res = new_res
    return res


def simples_avoiding(basis):
    """
    Yield all simple permutations that avoid basis.

    You may wish to use the 'Av' class from permuta for iterating over
    permutations that avoid a given basis.
    A naive approach to know when to terminate is to use the fact that every
    length n simple contains a simple of length n - 1 or length n - 2.
    """
    av = Av(basis)
    longest = 4
    length = 4
    while True:
        if length - 2 > longest:
            break
        for perm in av.of_length(length):
            if perm.is_simple():
                yield perm
                longest = length
        length += 1

def stretch_perms(perms, cells, obstruction=True):
    """Return all gridded perms with underlying perm in perms using cells."""
    if obstruction:
        GP = Obstruction
    else:
        GP = Requirement
    res = []
    for perm in perms:
        for embedding in embeddings(perm, cells):
            res.append(GP(perm, embedding))
    return res

def stretch_av_and_co(av, co, cells):
    """
    Return the obstruction and requirement implied by stretching all avoided
    and contained patterns.

    This will return a pair (O, R) where O is a list of gridded perms (of type
    Obstruction) and R is a list of lists of gridded perms (of type
    requirement).
    """
    return (stretch_perms(av, cells),
            [stretch_perms(c, cells, False) for c in co])


class SubDecomp(CombinatorialClass):
    """
    This is the base class for using the CombinatorialSpecificationSearcher.
    """
    def __init__(self):
        self.tiling = None

    def is_empty(self):
        return self.tiling.is_empty()

    def get_avoids_contains(self):
        if self.tiling.dimensions == (1, 1):
            return ([ob.patt for ob in self.tiling.obstructions],
                    [[r.patt for r in rq] for rq in self.tiling.requirements])

    def get_genf(self, **kwargs):
        """If it is the point tiling then return x else None."""
        if (self.tiling.is_point_tiling() and
            (isinstance(self, Point) or
             isinstance(self, SumIndecomposable) or
             isinstance(self, SkewDecomposable) or
             isinstance(self, All))):
            return x

    def get_min_poly(self, **kwargs):
        """If it is the point tiling then return x else None."""
        if (self.tiling.is_point_tiling() and
            (isinstance(self, Point) or
             isinstance(self, SumIndecomposable) or
             isinstance(self, SkewDecomposable) or
             isinstance(self, All))):
            return var('F') - x

    def objects_of_length(self, length):
        for gp in self.tiling.objects_of_length(length):
            yield gp.patt

    def to_jsonable(self):
        return self.tiling.to_jsonable()

    def __eq__(self, other):
        return type(self) == type(other) and self.tiling == other.tiling

    def __hash__(self):
        return hash(self.tiling)

    def __repr__(self):
        return repr(self.tiling)

    def __str__(self):
        res = self.__class__.__name__ + "\n"
        res += str(self.tiling)
        return res


class Point(SubDecomp):
    def __init__(self, avoids=tuple(), contains=tuple()):
        obs, reqs = stretch_av_and_co(avoids, contains, [(0, 0)])
        obs.extend([Obstruction.single_cell(Perm((0, 1)), (0, 0)),
                     Obstruction.single_cell(Perm((1, 0)), (0, 0))])
        reqs.extend([[Requirement.single_cell(Perm((0,)), (0, 0))]])
        self.tiling = Tiling(obs, reqs)


class All(SubDecomp):
    def __init__(self, avoids=tuple(), contains=tuple()):
        obs, reqs = stretch_av_and_co(avoids, contains, [(0, 0)])
        reqs.append([Requirement.single_cell(Perm((0,)), (0, 0))])
        self.tiling = Tiling(obs, reqs)


class SumDecomposable(SubDecomp):
    def __init__(self, avoids=tuple(), contains=tuple(), tiling=None):
        if tiling is not None and isinstance(tiling, Tiling):
            self.tiling = tiling
        else:
            obs, reqs = stretch_av_and_co(avoids, contains, [(0, 0), (1, 1)])
            reqs.extend([[Requirement.single_cell(Perm((0,)), (0, 0))],
                         [Requirement.single_cell(Perm((0,)), (1, 1))]])

            self.tiling = Tiling(obs, reqs)

    def is_empty(self):
        if any(ob.is_empty() for ob in self.tiling.obstructions):
            return True
        mxln = max(self.tiling.maximum_length_of_minimum_gridded_perm() + 4, 1)
        return all(
              gp.get_gridded_perm_in_cells([(0, 0)]).patt.is_sum_decomposable()
              for gp in self.tiling.gridded_perms(maxlen=mxln))

    @classmethod
    def from_tiling(cls, tiling):
        return SumDecomposable(tiling=tiling)

    def objects_of_length(self, length):
        for obj in self.tiling.objects_of_length(length):
            subob = obj.get_gridded_perm_in_cells([(0, 0)])
            if not subob.patt.is_sum_decomposable():
                yield obj.patt


class SkewDecomposable(SubDecomp):
    def __init__(self, avoids=tuple(), contains=tuple(), tiling=None):
        if tiling is not None and isinstance(tiling, Tiling):
            self.tiling = tiling
        else:
            obs, reqs = stretch_av_and_co(avoids, contains, [(0, 1), (1, 0)])
            reqs.extend([[Requirement.single_cell(Perm((0,)), (0, 1))],
                         [Requirement.single_cell(Perm((0,)), (1, 0))]])

            self.tiling = Tiling(obs, reqs)

    def is_empty(self):
        if any(ob.is_empty() for ob in self.tiling.obstructions):
            return True
        mxln = max(self.tiling.maximum_length_of_minimum_gridded_perm() + 4, 1)
        return all(
             gp.get_gridded_perm_in_cells([(0, 1)]).patt.is_skew_decomposable()
             for gp in self.tiling.gridded_perms(maxlen=mxln))

    @classmethod
    def from_tiling(cls, tiling):
        return SkewDecomposable(tiling=tiling)

    def objects_of_length(self, length):
        for obj in self.tiling.objects_of_length(length):
            subob = obj.get_gridded_perm_in_cells([(0, 1)])
            if not subob.patt.is_skew_decomposable():
                yield obj.patt


class SimpleInflation(SubDecomp):
    def __init__(self, perm=Perm(), avoids=tuple(), contains=tuple(),
                 tiling=None):
        if tiling is not None and isinstance(tiling, Tiling):
            self.tiling = tiling
        else:
            if not isinstance(perm, Perm) or not perm.is_simple():
                raise ValueError("The first argument must be a simple Perm.")
            cells = [(i, v) for i, v in enumerate(perm)]
            obs, reqs = stretch_av_and_co(avoids, contains, cells)
            reqs.extend([[Requirement.single_cell(Perm((0,)), cell)]
                         for cell in cells])
            self.tiling = Tiling(obs, reqs)

    @classmethod
    def from_tiling(cls, tiling):
        return SimpleInflation(tiling=tiling)


class SumIndecomposable(SubDecomp):
    def __init__(self, avoids=tuple(), contains=tuple()):
        obs, reqs = stretch_av_and_co(avoids, contains, [(0, 0)])
        reqs.append([Requirement.single_cell(Perm((0,)), (0, 0))])
        self.tiling = Tiling(obs, reqs)

    def objects_of_length(self, length):
        for obj in self.tiling.objects_of_length(length):
            if not obj.patt.is_sum_decomposable():
                yield obj.patt

    def is_empty(self):
        if any(ob.is_empty() for ob in self.tiling.obstructions):
            return True
        mxln = max(self.tiling.maximum_length_of_minimum_gridded_perm() + 4, 1)
        return all(gp.is_sum_decomposable()
                   for gp in self.tiling.gridded_perms(maxlen=mxln))


class SkewIndecomposable(SubDecomp):
    def __init__(self, avoids=tuple(), contains=tuple()):
        obs, reqs = stretch_av_and_co(avoids, contains, [(0, 0)])
        reqs.append([Requirement.single_cell(Perm((0,)), (0, 0))])
        self.tiling = Tiling(obs, reqs)

    def objects_of_length(self, length):
        for obj in self.tiling.objects_of_length(length):
            if not obj.patt.is_skew_decomposable():
                yield obj.patt

    def is_empty(self):
        if any(ob.is_empty() for ob in self.tiling.obstructions):
            return True
        mxln = max(self.tiling.maximum_length_of_minimum_gridded_perm() + 4, 1)
        return all(gp.is_skew_decomposable()
                   for gp in self.tiling.gridded_perms(maxlen=mxln))


def expansion(tiling, **kwargs):
    if isinstance(tiling, All):
        comb_classes = None
        #TODO: perform the substitution decomposition
        # You may wish to use the get_avoids_contains method.
        av, co = tiling.get_avoids_contains()
        comb_classes = [cls(av, co)
                        for cls in [Point, SumDecomposable, SkewDecomposable]]
        for simple in simples_avoiding(av):
            comb_classes.append(SimpleInflation(simple, av, co))
        if comb_classes is not None:
            yield BatchRule("Appropriate description", comb_classes)
    elif isinstance(tiling, SumIndecomposable):
        comb_classes = None
        #TODO: perform the substitution decomposition.
        # You may wish to use the get_avoids_contains method.

        av, co = tiling.get_avoids_contains()
        comb_classes = [cls(av, co)
                        for cls in [Point, SkewDecomposable]]
        for simple in simples_avoiding(av):
            comb_classes.append(SimpleInflation(simple, av, co))

        if comb_classes is not None:
            yield BatchRule("Appropriate description", comb_classes)
    elif isinstance(tiling, SkewIndecomposable):
        comb_classes = None
        #TODO: perform the substitution decomposition.
        # You may wish to use the get_avoids_contains method.

        av, co = tiling.get_avoids_contains()
        comb_classes = [cls(av, co)
                        for cls in [Point, SumDecomposable]]
        for simple in simples_avoiding(av):
            comb_classes.append(SimpleInflation(simple, av, co))

        if comb_classes is not None:
            yield BatchRule("Appropriate description", comb_classes)


def factor(tiling, **kwargs):
    if (isinstance(tiling, SumDecomposable) or
        isinstance(tiling, SkewDecomposable) or
            isinstance(tiling, SimpleInflation)):
        if (all(gp.is_single_cell()
                for gp in chain(tiling.tiling.obstructions,
                                *tiling.tiling.requirements)) and
            all(len(req_list) == 1
                for req_list in tiling.tiling.requirements)):

            comb_classes = []
            for cell, (av, co) in tiling.tiling.cell_basis().items():
                if len(av) == 1 and len(av[0]) == 1:
                    raise ValueError("This shouldn't happen")
                co = [[p] for p in co]
                # TODO: perform the substitution decomposition, you will need
                # to consider the assumptions made depending on whether this is
                # SumDecomposable, SkewDecomposable, or a SimpleInflation
                if (isinstance(tiling, SimpleInflation) or
                    (isinstance(tiling, SumDecomposable) and cell == (1, 1)) or
                    (isinstance(tiling, SkewDecomposable) and
                     cell == (1, 0))):
                    comb_classes.append(All(av, co))
                elif isinstance(tiling, SumDecomposable):
                    if cell != (0, 0):
                        raise ValueError("This shouldn't happen")
                    comb_classes.append(SumIndecomposable(av, co))
                elif isinstance(tiling, SkewDecomposable):
                    if cell != (0, 1):
                        raise ValueError("This shouldn't happen")
                    comb_classes.append(SkewIndecomposable(av, co))
                else:
                    raise ValueError("This shouldn't happen")
            if comb_classes:
                yield DecompositionRule("Factor", comb_classes)


def all_factor_insertions(tiling, **kwargs):
    if (isinstance(tiling, SumDecomposable) or
        isinstance(tiling, SkewDecomposable) or
            isinstance(tiling, SimpleInflation)):
        for gp in sorted(set(chain(tiling.tiling.obstructions,
                                   *tiling.tiling.requirements))):
            factors = gp.factors()
            if len(factors) != 1:
                for gp in factors:
                    av = tiling.tiling.add_obstruction(gp.patt, gp.pos)
                    co = tiling.tiling.add_requirement(gp.patt, gp.pos)
                    comb_classes = [tiling.__class__.from_tiling(av),
                                    tiling.__class__.from_tiling(co)]
                    yield Rule(formal_step="Insert {}.".format(str(gp)),
                               comb_classes=comb_classes,
                               ignore_parent=True,
                               inferable=[True for _ in range(2)],
                               possibly_empty=[True for _ in range(2)],
                               workable=[True for _ in range(2)],
                               constructor='disjoint')
                    break
                break

def list_cleanup(tiling, **kwargs):
    for gp in chain(*[req_list
                      for req_list in tiling.tiling.requirements
                      if len(req_list) > 1]):
        av = tiling.tiling.add_obstruction(gp.patt, gp.pos)
        co = tiling.tiling.add_requirement(gp.patt, gp.pos)
        comb_classes = [tiling.__class__.from_tiling(av),
                        tiling.__class__.from_tiling(co)]
        yield Rule(formal_step="Insert {}.".format(str(gp)),
                   comb_classes=comb_classes,
                   ignore_parent=True,
                   inferable=[True for _ in range(2)],
                   possibly_empty=[True for _ in range(2)],
                   workable=[True for _ in range(2)],
                   constructor='disjoint')
        break


def verify_point(tiling, **kwargs):
    """Verify exactly the point tiling."""
    if (tiling.tiling.is_point_tiling()):
        if (isinstance(tiling, Point) or
            isinstance(tiling, SumIndecomposable) or
            isinstance(tiling, SkewDecomposable) or
                isinstance(tiling, All)):
            return VerificationRule("its the point")


pack = StrategyPack(initial_strats=[factor, list_cleanup,
                                    all_factor_insertions],
                    inferral_strats=[],
                    expansion_strats=[[expansion]],
                    ver_strats=[verify_point],
                    name=("substition_decomposition"))


if __name__ == "__main__":
    basis = input("Enter comma separated permutations: ")
    basis = [Perm.to_standard(p) for p in basis.split(',')]

    start_class = All(basis)
    searcher = CombinatorialSpecificationSearcher(start_class, pack,
                                                  debug=True)
    tree = searcher.auto_search(status_update=30)

    tree.get_min_poly(solve=True)
