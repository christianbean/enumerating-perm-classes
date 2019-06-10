"""
A demo file for Permutation Pattern 2019 pre-conference workshop for the
computational mathematics line on automatic methods in enumerating permutation
classes, given by Christian Bean. This demo allows you to implement your own
version of an algorithm that can find regular insertion encodings. It uses
the permuta and comb_spec_searcher modules from the PermutaTriangle.
https://github.com/PermutaTriangle

For this file I recommend using the notation 'l_1 m_1 r_2 f_1 f_1', so space
separated letters with '_' separation from type and slot index.

To iterate over a word one can then do
for letter in s.split(' '):
    t, i = letter.split('_')

You will need to implement the following functions:
    Configuration
        - extend_by_letter
        - perms_of_length
        - to_prefix
    Suffixes
        - equivalent_configs
        - is_empty
        - objects_of_length
"""
from sympy import var
from sympy.abc import x

from comb_spec_searcher import (BatchRule, CombinatorialClass,
                                CombinatorialSpecificationSearcher,
                                DecompositionRule, Rule, StrategyPack,
                                VerificationRule)
from permuta import Perm, PermSet
from permuta.descriptors import Basis


class Configuration:
    def __init__(self, patt, slots):
        self.patt = patt
        self.slots = tuple(sorted(set(slots)))
        if (not isinstance(self.patt, Perm) and
            not all((isinstance(i, int) and 0 <= i <= len(patt))
                    for i in self.slots)):
            raise TypeError(("A configuration takes a 'Perm' object and a "
                             "tuple of integers 0 <= len(patt)."))

    def extend_by_letter(self, letter):
        """Return configuration reached by next reading letter. You may wish
        to use the Perm.insert method."""
        pass

    def perms_of_length(self, length):
        """
        Yield all permutations coming from this configuration.

        You may wish to use the PermSet class. PermSet(i) gives all
        permutations of length i.
        """
        pass

    def to_prefix(self):
        """Return the prefix corresponding to the configuration."""
        pass

    @classmethod
    def from_prefix(cls, prefix):
        """Return configuration corresponding to prefix."""
        return prefix

    def __eq__(self, other):
        return self.patt == other.patt and self.slots == other.slots

    def __len__(self):
        return len(self.patt) + len(self.slots)

    def __repr__(self):
        return "Configuration({}, {})".format(
                                            repr(self.patt), repr(self.slots))

    def __str__(self):
        return ("".join(str(v) if i not in self.slots else "\u2666" + str(v)
                        for i, v in enumerate(self.patt)) +
                ("\u2666" if len(self.patt) in self.slots else ""))


class Suffixes(CombinatorialClass):
    """This combinatorial class represents the set of all valid suffixes for a
    given configuration that avoid a given basis."""
    def __init__(self, configuration, basis, last_letter=None):
        """The last_letter is used to build up the words. We will not in fact
        use this, and any time an instance of this class contains a last_letter
        many of our mehods will do nothing."""
        if not isinstance(configuration, Configuration):
            raise TypeError("Expected value of type Configuration.")
        self.config = configuration
        self.basis = Basis(basis)
        self.last_letter = last_letter

    def equivalent_configs(self):
        """Yield all configuration that are seen to be equivalent by removing
        one element. You may wish to use the method Perm.remove."""
        pass

    def is_empty(self):
        """Return True if there are no suffixes of any length with this
        configuration avoiding the patterns."""
        pass

    def get_genf(self, **kwargs):
        if self.last_letter is None and not self.config.slots:
            return x**0

    def get_min_poly(self, **kwargs):
        if self.last_letter is None and not self.config.slots:
            return var('F') - x**0

    def objects_of_length(self, length):
        """Yield all valid suffixes of given length."""
        pass

    def to_jsonable(self):
        return {'basis': tuple(tuple(p) for p in self.basis),
                'config': (tuple(self.config.patt), tuple(self.config.slots)),
                'last_letter': str(self.last_letter)}

    def __eq__(self, other):
        return (self.basis == other.basis and self.config == other.config and
                self.last_letter == other.last_letter)

    def __hash__(self):
        return hash(hash(self.config.patt) + hash(self.config.slots) +
                    hash(self.basis) + hash(self.last_letter))

    def __repr__(self):
        return "Suffixes({}, {}, {})".format(repr(self.config),
                                             repr(tuple(self.basis)),
                                             repr(self.last_letter))

    def __str__(self):
        return "{} avoiding {}".format(self.config, self.basis)


class Letter(CombinatorialClass):
    def __init__(self, letter):
        if not isinstance(letter, str):
            raise TypeError("Expected value of type str.")
        if " " in letter:
            raise ValueError("Should be a single letter.")
        self.letter = letter

    def is_empty(self):
        return False

    def get_genf(self, **kwargs):
        return x

    def get_min_poly(self, **kwargs):
        return var('F') - x

    def objects_of_length(self, length):
        if length == 1:
            yield self.letter

    def to_jsonable(self):
        return {'letter': str(self.letter)}

    def __eq__(self, other):
        return self.letter == other.letter

    def __hash__(self):
        return hash(self.letter)

    def __repr__(self):
        return "Letter({})".format(self.letter)

    def __str__(self):
        return "The letter '{}'".format(self.letter)


def equivalent(av_config, **kwargs):
    """Yield equivalence rules of the configurations that are the same by
    some point being removed."""
    if av_config.last_letter is None:
        for config in av_config.equivalent_configs():
            yield Rule("The configurations are equivalent",
                       [Suffixes(config, av_config.basis)],
                       [True], [False], [True], ignore_parent=True,
                       constructor='equiv')


def expansion(av_config, **kwargs):
    """Yield the batch rule that comes from reading the next symbol."""
    if isinstance(av_config, Suffixes) and av_config.last_letter is None:
        comb_classes = []
        config = av_config.config
        for letter in ('l', 'r', 'm', 'f'):
            for i in range(len(config.slots)):
                l = letter + "_" + str(i)
                extended = config.extend_by_letter(l)
                new_comb_class = Suffixes(extended, basis, l)
                comb_classes.append(new_comb_class)
        yield BatchRule("Inserting next letter.", comb_classes)


def remove_letter(av_config, **kwargs):
    """Yield the decomposition rule of removing the last letter read."""
    if isinstance(av_config, Suffixes) and av_config.last_letter is not None:
        yield DecompositionRule("Removing last letter.",
                                [Letter(av_config.last_letter),
                                 Suffixes(av_config.config, av_config.basis)])


def verify_letters_and_perms(config, **kwargs):
    if isinstance(config, Letter):
        return VerificationRule("Its a letter.")
    elif config.last_letter is None and len(config.config.slots) == 0:
        return VerificationRule("Its a permutation.")

pack = StrategyPack(initial_strats=[remove_letter, equivalent],
                    inferral_strats=[],
                    expansion_strats=[[expansion]],
                    ver_strats=[verify_letters_and_perms],
                    name=("Finding regular insertion encodings"))

if __name__ == "__main__":
    from permuta.permutils import is_insertion_encodable_maximum

    basis = input("Enter comma separated permutations: ")
    basis = [Perm.to_standard(p) for p in basis.split(',')]

    if is_insertion_encodable_maximum(basis):
        start_class = Suffixes(Configuration(Perm(), (0,)), basis)
        print(Configuration(Perm((0,)), (0,)))
        searcher = CombinatorialSpecificationSearcher(start_class, pack,
                                                      debug=True)
        tree = searcher.auto_search(status_update=10)
        tree.get_min_poly(solve=True)
    else:
        print("Not insertion encodable")
