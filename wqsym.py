# -*- coding: utf-8 -*-
r"""
Word Quasi-symmetric functions

AUTHORS:

- Travis Scrimshaw (2018-04-09): initial implementation
- Darij Grinberg and Amy Pang (2018-04-12): further bases and methods

TESTS:

We check that the coercion `C \to M` goes through the `X` basis::

    sage: WQSym = algebras.WQSym(QQ)
    sage: Q = WQSym.Q()
    sage: C = WQSym.C()
    sage: M = WQSym.M()
    sage: M.coerce_map_from(C)
    Composite map:
      From: Word Quasi-symmetric functions over Rational Field in the Cone basis
      To:   Word Quasi-symmetric functions over Rational Field in the Monomial basis
      Defn:   Generic morphism:
              From: Word Quasi-symmetric functions over Rational Field in the Cone basis
              To:   Word Quasi-symmetric functions over Rational Field in the Characteristic basis
            then
              Generic morphism:
              From: Word Quasi-symmetric functions over Rational Field in the Characteristic basis
              To:   Word Quasi-symmetric functions over Rational Field in the Monomial basis
"""

# ****************************************************************************
#       Copyright (C) 2018 Travis Scrimshaw <tcscrims at gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
# ****************************************************************************

from sage.misc.cachefunc import cached_method, cached_function
from sage.misc.bindable_class import BindableClass
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.functional import symbolic_prod
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.global_options import GlobalOptions
from sage.categories.tensor import tensor
from sage.categories.cartesian_product import cartesian_product
from sage.categories.hopf_algebras import HopfAlgebras
from sage.categories.realizations import Category_realization_of_parent
from sage.combinat.free_module import CombinatorialFreeModule
from sage.combinat.set_partition import SetPartition
from sage.combinat.set_partition_ordered import OrderedSetPartitions, OrderedSetPartition
from sage.combinat.shuffle import ShuffleProduct_overlapping, ShuffleProduct
from sage.combinat.ordered_tree import LabelledOrderedTree
from sage.rings.integer_ring import ZZ
from copy import copy
from packed_words import PackedWords, PackedWord


class WQSymBasis_abstract(CombinatorialFreeModule, BindableClass):
    """
    Abstract base class for bases of `WQSym`.

    This must define two attributes:

    - ``_prefix`` -- the basis prefix
    - ``_basis_name`` -- the name of the basis (must match one
      of the names that the basis can be constructed from `WQSym`)
    """
    def __init__(self, alg, graded=True):
        r"""
        Initialize ``self``.

        EXAMPLES::

            sage: M = algebras.WQSym(QQ).M()
            sage: TestSuite(M).run()  # long time
        """
        CombinatorialFreeModule.__init__(self, alg.base_ring(),
                                         OrderedSetPartitions(),
                                         category=WQSymBases(alg, graded),
                                         bracket="", prefix=self._prefix)

    def _repr_term(self, osp):
        r"""
        Return a string representation of an element of WordQuasiSymmetricFunctions
        in the basis ``self``.

        TESTS::

            sage: M = WordQuasiSymmetricFunctions(QQ).M()
            sage: elt = M[[[1,2]]] * M[[[1]]]; elt
            M[{1, 2}, {3}] + M[{1, 2, 3}] + M[{3}, {1, 2}]
            sage: M.options.objects = "words"
            sage: elt
            M[1, 1, 2] + M[1, 1, 1] + M[2, 2, 1]
            sage: M.options._reset()
        """
        return self._prefix + self.options._dispatch(self, '_repr_', 'objects', osp)

    def _repr_compositions(self, osp):
        """
        Return a string representation of ``osp`` indexed by ordered set partitions.

        This method is called by ``self_repr_term``.

        EXAMPLES::

            sage: M = WordQuasiSymmetricFunctions(QQ).M()
            sage: elt = M[[[1,2]]] * M[[[1]]]; elt
            M[{1, 2}, {3}] + M[{1, 2, 3}] + M[{3}, {1, 2}]
            sage: M.options.display = "tight"
            sage: elt
            M[{1,2},{3}] + M[{1,2,3}] + M[{3},{1,2}]
            sage: M.options.display = "compact"
            sage: elt
            M[12.3] + M[123] + M[3.12]
            sage: osp = OrderedSetPartition([[2,4], [1,3,7],[5,6]])
            sage: M._repr_compositions(osp) == '[24.137.56]'
            True
            sage: M.options._reset(); elt
            M[{1, 2}, {3}] + M[{1, 2, 3}] + M[{3}, {1, 2}]
        """
        display = self.options.display
        disp = repr(osp)
        if display == 'tight':
            disp = disp.replace(", ", ",")
            return disp
        elif display == 'compact':
            disp = disp.replace("}, ", ".").replace("}", "").replace("{", "")
            return disp.replace(", ", "")
        else:
            # treat display as 'normal'
            return disp

    def _repr_words(self, osp):
        """
        Return a string representation of ``self`` indexed by packed words.

        This method is called by ``self_repr_term``.

        EXAMPLES::

            sage: M = WordQuasiSymmetricFunctions(QQ).M()
            sage: elt = M[[[1,2]]]*M[[[1]]]; elt
            M[{1, 2}, {3}] + M[{1, 2, 3}] + M[{3}, {1, 2}]
            sage: M.options.objects = "words"
            sage: elt
            M[1, 1, 2] + M[1, 1, 1] + M[2, 2, 1]
            sage: M.options.display = "tight"
            sage: elt
            M[1,1,2] + M[1,1,1] + M[2,2,1]
            sage: M.options.display = "compact"
            sage: elt
            M[112] + M[111] + M[221]
            sage: osp = OrderedSetPartition([[2,4], [1,3,7],[5,6]])
            sage: M._repr_words(osp) == '[2121332]'
            True
            sage: M.options._reset(); elt
            M[{1, 2}, {3}] + M[{1, 2, 3}] + M[{3}, {1, 2}]
        """
        display = self.options.display
        disp = repr(list(osp.to_packed_word()))
        if display == 'tight':
            return disp.replace(", ", ",")
        elif display == 'compact':
            return disp.replace(", ", "")
        else:
            # treat display as 'normal'
            return disp

    def _repr_forests(self, osp):
        """
        Return a string representation of ``self`` indexed by forests.

        This method is called by ``self_repr_term``.

        EXAMPLES::

            sage: M = WordQuasiSymmetricFunctions(QQ).M()
            sage: elt = M[[[1,2]]]*M[[[1]]]; elt
            M[{1, 2}, {3}] + M[{1, 2, 3}] + M[{3}, {1, 2}]
            sage: M.options.objects = "forests"
            sage: elt
            M[0[0*[0[]]]] + M[0*[0*[0[]]]] + M[0*[0[]], 0[]]
            sage: M.options.display = "ascii_art"
            sage: elt
            M[ 0  ]
            [ |  ]
            [ 0* ]
            [ |  ]
            [ 0  ] + M[ 0* ]
            [ |  ]
            [ 0* ]
            [ |  ]
            [ 0  ] + M[ 0*, 0 ]
            [ |     ]
            [ 0     ]
####
            M[ 0  ] + M[ 0* ] + M[ 0*, 0 ]
             [ |  ]    [ |  ]    [ |     ]
             [ 0* ]    [ 0* ]    [ 0     ]
             [ |  ]    [ |  ]
             [ 0  ]    [ 0  ]
            sage: M.options._reset(); elt
            M[{1, 2}, {3}] + M[{1, 2, 3}] + M[{3}, {1, 2}]
        """
        #import pdb; pdb.set_trace()
        display = self.options.display
        obj = PackedWord(osp.to_packed_word()).packed_word_to_labelled_forest()
        if display == 'ascii_art':
            from sage.typeset.ascii_art import ascii_art
            return str(ascii_art(obj))
        return repr(obj)

    def _ascii_art_term(self, osp):
        """TODO
            sage: P = WordQuasiSymmetricFunctions(QQ).P()
            sage: O = WordQuasiSymmetricFunctions(QQ).O()
            sage: Pelt = P[[[1,2]]]*P[[[1]]]; Pelt
            sage: Oelt = O[[[1,2]]]*O[[[1]]]; Oelt
            sage: ascii_art(Pelt)
            sage: ascii_art(Oelt)

        """
        if self._prefix == "P":
            res = PackedWord(osp.to_packed_word()).packed_word_to_labelled_forest()
        elif self._prefix == "O":
            res = PackedWord(osp.to_packed_word()).packed_word_to_labelled_forest_left()
        else:
            raise NotImplementedError
        from sage.typeset.ascii_art import ascii_art
        return ascii_art(res)#, baseline = "top")

    def _coerce_map_from_(self, R):
        r"""
        Return ``True`` if there is a coercion from ``R`` into ``self``
        and ``False`` otherwise.

        The things that coerce into ``self`` are

        - word quasi-symmetric functions over a base with
          a coercion map into ``self.base_ring()``

        EXAMPLES::

            sage: M = algebras.WQSym(GF(7)).M(); M
            Word Quasi-symmetric functions over Finite Field of size 7 in the Monomial basis

        Elements of the word quasi-symmetric functions canonically coerce in::

            sage: x, y = M([[1]]), M([[2,1]])
            sage: M.coerce(x+y) == x+y
            True

        The word quasi-symmetric functions over `\ZZ` coerces in,
        since `\ZZ` coerces to `\GF{7}`::

            sage: N = algebras.WQSym(ZZ).M()
            sage: Nx, Ny = N([[1]]), N([[2,1]])
            sage: z = M.coerce(Nx+Ny); z
            M[{1}] + M[{1, 2}]
            sage: z.parent() is M
            True

        However, `\GF{7}` does not coerce to `\ZZ`, so word
        quasi-symmetric functions over `\GF{7}` does not coerce
        to the same algebra over `\ZZ`::

            sage: N.coerce(y)
            Traceback (most recent call last):
            ...
            TypeError: no canonical coercion from Word Quasi-symmetric functions
             over Finite Field of size 7 in the Monomial basis to
             Word Quasi-symmetric functions over Integer Ring in the Monomial basis

        TESTS::

            sage: M = algebras.WQSym(ZZ).M()
            sage: N = algebras.WQSym(QQ).M()
            sage: M.has_coerce_map_from(N)
            False
            sage: N.has_coerce_map_from(M)
            True
            sage: M.has_coerce_map_from(QQ)
            False
            sage: N.has_coerce_map_from(QQ)
            True
            sage: M.has_coerce_map_from(PolynomialRing(ZZ, 3, 'x,y,z'))
            False
        """
        # word quasi-symmetric functions in the same variables
        # over any base that coerces in:
        if isinstance(R, WQSymBasis_abstract):
            if R.realization_of() == self.realization_of():
                return True
            if not self.base_ring().has_coerce_map_from(R.base_ring()):
                return False
            if self._basis_name == R._basis_name:  # The same basis
                def coerce_base_ring(self, x):
                    return self._from_dict(x.monomial_coefficients())
                return coerce_base_ring
            # Otherwise lift that basis up and then coerce over
            target = getattr(self.realization_of(), R._basis_name)()
            return self._coerce_map_via([target], R)
        return super(WQSymBasis_abstract, self)._coerce_map_from_(R)

    @cached_method
    def an_element(self):
        """
        Return an element of ``self``.

        EXAMPLES::

            sage: M = algebras.WQSym(QQ).M()
            sage: M.an_element()
            M[{1}] + 2*M[{1}, {2}]
        """
        return self([[1]]) + 2*self([[1],[2]])

    def some_elements(self):
        """
        Return some elements of the word quasi-symmetric functions.

        EXAMPLES::

            sage: M = algebras.WQSym(QQ).M()
            sage: M.some_elements()
            [M[], M[{1}], M[{1, 2}],
             M[{1}] + M[{1}, {2}],
             M[] + 1/2*M[{1}]]
        """
        u = self.one()
        o = self([[1]])
        s = self.base_ring().an_element()
        return [u, o, self([[1,2]]), o + self([[1],[2]]), u + s*o]
    
    def prod_dend(self, l,i):
        """
            sage: R = algebras.WQSym(QQ).R()
            sage: R.options.objects = 'words'
            sage: l = [R[1],R[1],R[1],R[1]]
            sage: R.prod_dend(l,0)
            R[2, 3, 4, 1]
            sage: R.prod_dend(l,1)
            R[1, 3, 4, 2] + R[3, 1, 4, 2] + R[3, 4, 1, 2]
        """
        l = copy(l)
        if len(l) == 1:
            return l[0]
        if i == -1:
            l[1] = self.right_product(l[0], l[1])
            return self.prod_dend(l[1:], -1)
        if i == 0:
            return self.left_product(l[-1], self.prod_dend(l[:-1], -1))
        if i == 1:
            return self.right_product(l[0], self.prod_dend(l[1:], 0))
        else:
            l[i-2] = self.left_product(l[i-2], l[i-1])
            return self.prod_dend(l[:i-1] + l[i:], i-1)
        
    def brackets(self, l):
        """
            sage: l = [R[1],R[1],R[1],R[1]]
            sage: R.brackets(l)
            R[1, 3, 4, 2] - R[2, 1, 4, 3] + R[3, 1, 4, 2] - R[2, 4, 1, 3] + R[3, 2, 1, 4] - R[4, 2, 1, 3] + R[3, 4, 1, 2] - R[2, 3, 4, 1]
        """
        res = 0
        n = len(l)
        for i in range(n):
            p = self.prod_dend(l, i)
            res += (-1)**(n-1-i) * p
        return res


    def prod_concat(self, l,i):
        """
            sage: R = algebras.WQSym(QQ).R()
            sage: R.options.objects = 'words'
            sage: l = [R[1],R[1],R[1],R[1]]
            sage: R.prod_concat(l,0)
            R[2, 3, 4, 1]
            sage: R.prod_concat(l,1)
            R[1, 3, 4, 2]
        """
        l = copy(l)
        if len(l) == 1:
            return l[0]
        if i == -1:
            l[1] = l[0].right_shifted_concat(l[1])
            return self.prod_concat(l[1:], -1)
        if i == 0:
            return l[-1].left_shifted_concat(self.prod_concat(l[:-1], -1))
        if i == 1:
            return l[0].right_shifted_concat(self.prod_concat(l[1:], 0))
        else:
            l[i-2] = l[i-1].left_shifted_concat(l[i-1])
            return self.prod_concat(l[:i-1] + l[i:], i-1)
        
    def brackets_concat(self, l):
        """
            sage: l = [R[1],R[1],R[1],R[1]]
            sage: R.brackets_concat(l)
            R[1, 3, 4, 2] - R[2, 1, 4, 3] - R[2, 3, 4, 1] + R[4, 3, 2, 1, 5]
        """
        res = 0
        n = len(l)
        for i in range(n):
            p = self.prod_concat(l, i)
            res += (-1)**(n-1-i) * p
        return res




class WordQuasiSymmetricFunctions(UniqueRepresentation, Parent):
    r"""
    The word quasi-symmetric functions.

    The ring of word quasi-symmetric functions can be defined as a
    subring of the ring of all bounded-degree noncommutative power
    series in countably many indeterminates (i.e., elements in
    `R \langle \langle x_1, x_2, x_3, \ldots \rangle \rangle` of bounded
    degree). Namely, consider words over the alphabet `\{1, 2, 3, \ldots\}`;
    every noncommutative power series is an infinite `R`-linear
    combination of these words.
    For each such word `w`, we define the *packing* of `w` to be the
    word `\operatorname{pack}(w)` that is obtained from `w` by replacing
    the smallest letter that appears in `w` by `1`, the second-smallest
    letter that appears in `w` by `2`, etc. (for example,
    `\operatorname{pack}(4112774) = 3112443`).
    A word `w` is said to be *packed* if `\operatorname{pack}(w) = w`.
    For each packed word `u`, we define the noncommutative power series
    `\mathbf{M}_u = \sum w`, where the sum ranges over all words `w`
    satisfying `\operatorname{pack}(w) = u`.
    The span of these power series `\mathbf{M}_u` is a subring of the
    ring of all noncommutative power series; it is called the ring of
    word quasi-symmetric functions, and is denoted by `WQSym`.

    For each nonnegative integer `n`, there is a bijection between
    packed words of length `n` and ordered set partitions of
    `\{1, 2, \ldots, n\}`. Under this bijection, a packed word
    `u = (u_1, u_2, \ldots, u_n)` of length `n` corresponds to the
    ordered set partition `P = (P_1, P_2, \ldots, P_k)` of
    `\{1, 2, \ldots, n\}` whose `i`-th part `P_i` (for each `i`) is the
    set of all `j \in \{1, 2, \ldots, n\}` such that `u_j = i`.

    The basis element `\mathbf{M}_u` is also denoted as `\mathbf{M}_P`
    in this situation. The basis `(\mathbf{M}_P)_P` is called the
    *Monomial basis* and is implemented as
    :class:`~sage.combinat.chas.wqsym.WordQuasiSymmetricFunctions.Monomial`.

    Other bases are the cone basis (aka C basis), the characteristic
    basis (aka X basis), the Q basis and the Phi basis.

    Bases of `WQSym` are implemented (internally) using ordered set
    partitions. However, the user may access specific basis vectors using
    either packed words or ordered set partitions. See the examples below,
    noting especially the section on ambiguities.

    `WQSym` is endowed with a connected graded Hopf algebra structure (see
    Section 2.2 of [NoThWi08]_, Section 1.1 of [FoiMal14]_ and
    Section 4.3.2 of [MeNoTh11]_) given by

    .. MATH::

        \Delta(\mathbf{M}_{(P_1,\ldots,P_{\ell})}) = \sum_{i=0}^{\ell}
            \mathbf{M}_{\operatorname{st}(P_1, \ldots, P_i)} \otimes
            \mathbf{M}_{\operatorname{st}(P_{i+1}, \ldots, P_{\ell})}.

    Here, for any ordered set partition `(Q_1, \ldots, Q_k)` of a
    finite set `Z` of integers, we let `\operatorname{st}(Q_1, \ldots, Q_k)`
    denote the set partition obtained from `Z` by replacing the smallest
    element appearing in it by `1`, the second-smallest element by `2`,
    and so on.

    A rule for multiplying elements of the monomial basis relies on the
    *quasi-shuffle product* of two ordered set partitions.
    The quasi-shuffle product `\Box` is given by
    :class:`~sage.combinat.shuffle.ShuffleProduct_overlapping` with the
    ``+`` operation in the overlapping of the shuffles being the
    union of the sets.  The product `\mathbf{M}_P \mathbf{M}_Q`
    for two ordered set partitions `P` and `Q` of `[n]` and `[m]`
    is then given by

    .. MATH::

        \mathbf{M}_P \mathbf{M}_Q
        = \sum_{R \in P \Box Q^+} \mathbf{M}_R ,

    where `Q^+` means `Q` with all numbers shifted upwards by `n`.

    Sometimes, `WQSym` is also denoted as `NCQSym`.

    REFERENCES:

    - [FoiMal14]_
    - [MeNoTh11]_
    - [NoThWi08]_
    - [BerZab05]_

    EXAMPLES:

    Constructing the algebra and its Monomial basis::

        sage: WQSym = algebras.WQSym(ZZ)
        sage: WQSym
        Word Quasi-symmetric functions over Integer Ring
        sage: M = WQSym.M()
        sage: M
        Word Quasi-symmetric functions over Integer Ring in the Monomial basis
        sage: M[[]]
        M[]

    Calling basis elements using packed words::

        sage: x = M[1,2,1]; x
        M[{1, 3}, {2}]
        sage: x == M[[1,2,1]] == M[Word([1,2,1])]
        True
        sage: y = M[1,1,2] - M[1,2,2]; y
        -M[{1}, {2, 3}] + M[{1, 2}, {3}]

    Calling basis elements using ordered set partitions::

        sage: z = M[[1,2,3],]; z
        M[{1, 2, 3}]
        sage: z == M[[[1,2,3]]] == M[OrderedSetPartition([[1,2,3]])]
        True
        sage: M[[1,2],[3]]
        M[{1, 2}, {3}]

    Note that expressions above are output in terms of ordered set partitions,
    even when input as packed words. Output as packed words can be achieved
    by modifying the global options. (See :meth:`OrderedSetPartitions.options`
    for further details.)::

        sage: M.options.objects = "words"
        sage: y
        -M[1, 2, 2] + M[1, 1, 2]
        sage: M.options.display = "compact"
        sage: y
        -M[122] + M[112]
        sage: z
        M[111]

    The options should be reset to display as ordered set partitions::

        sage: M.options._reset()
        sage: z
        M[{1, 2, 3}]

    Illustration of the Hopf algebra structure::

        sage: M[[2, 3], [5], [6], [4], [1]].coproduct()
        M[] # M[{2, 3}, {5}, {6}, {4}, {1}] + M[{1, 2}] # M[{3}, {4}, {2}, {1}]
         + M[{1, 2}, {3}] # M[{3}, {2}, {1}] + M[{1, 2}, {3}, {4}] # M[{2}, {1}]
         + M[{1, 2}, {4}, {5}, {3}] # M[{1}] + M[{2, 3}, {5}, {6}, {4}, {1}] # M[]
        sage: _ == M[5,1,1,4,2,3].coproduct()
        True
        sage: M[[1,1,1]] * M[[1,1,2]]   # packed words
        M[{1, 2, 3}, {4, 5}, {6}] + M[{1, 2, 3, 4, 5}, {6}]
         + M[{4, 5}, {1, 2, 3}, {6}] + M[{4, 5}, {1, 2, 3, 6}]
         + M[{4, 5}, {6}, {1, 2, 3}]
        sage: M[[1,2,3],].antipode()  # ordered set partition
        -M[{1, 2, 3}]
        sage: M[[1], [2], [3]].antipode()
        -M[{1, 2, 3}] - M[{2, 3}, {1}] - M[{3}, {1, 2}] - M[{3}, {2}, {1}]
        sage: x = M[[1],[2],[3]] + 3*M[[2],[1]]
        sage: x.counit()
        0
        sage: x.antipode()
        3*M[{1}, {2}] + 3*M[{1, 2}] - M[{1, 2, 3}] - M[{2, 3}, {1}]
         - M[{3}, {1, 2}] - M[{3}, {2}, {1}]

    .. rubric:: Ambiguities

    Some ambiguity arises when accessing basis vectors with the dictionary syntax,
    i.e., ``M[...]``. A common example is when referencing an ordered set partition
    with one part. For example, in the expression ``M[[1,2]]``, does ``[[1,2]]``
    refer to an ordered set partition or does ``[1,2]`` refer to a packed word?
    We choose the latter: if the received arguments do not behave like a tuple of
    iterables, then view them as describing a packed word. (In the running example,
    one argument is received, which behaves as a tuple of integers.) Here are a
    variety of ways to get the same basis vector::

        sage: x = M[1,1]; x
        M[{1, 2}]
        sage: x == M[[1,1]]  # treated as word
        True
        sage: x == M[[1,2],] == M[[[1,2]]]  # treated as ordered set partitions
        True

        sage: M[[1,3],[2]]  # treat as ordered set partition
        M[{1, 3}, {2}]
        sage: M[[1,3],[2]] == M[1,2,1]  # treat as word
        True

    TESTS::

        sage: M = WordQuasiSymmetricFunctions(QQ).M()
        sage: a = M[OrderedSetPartition([[1]])]
        sage: b = M[OrderedSetPartitions(1)([[1]])]
        sage: c = M[[1]]
        sage: a == b == c
        True

    .. TODO::

        - Dendriform structure.
    """
    def __init__(self, R):
        """
        Initialize ``self``.

        TESTS::

            sage: A = algebras.WQSym(QQ)
            sage: TestSuite(A).run()  # long time
        """
        category = HopfAlgebras(R).Graded().Connected()
        Parent.__init__(self, base=R, category=category.WithRealizations())

    def _repr_(self):
        """
        Return the string representation of ``self``.

        EXAMPLES::

            sage: algebras.WQSym(QQ)  # indirect doctest
            Word Quasi-symmetric functions over Rational Field
        """
        return "Word Quasi-symmetric functions over {}".format(self.base_ring())

    def a_realization(self):
        r"""
        Return a particular realization of ``self`` (the `M`-basis).

        EXAMPLES::

            sage: WQSym = algebras.WQSym(QQ)
            sage: WQSym.a_realization()
            Word Quasi-symmetric functions over Rational Field in the Monomial basis
        """
        return self.M()

    _shorthands = tuple(['M', 'X', 'C', 'Q', 'Phi', 'O', 'P', 'R', 'GL', 'SR'])

    # add options to class
    class options(GlobalOptions):
        r"""
        Set and display the global options for bases of WordQuasiSymmetricFunctions.
        If no parameters are set, then the function returns a copy of the options
        dictionary.

        The ``options`` can be accessed as the method
        :obj:`WordQuasiSymmetricFunctions.options` of
        :class:`WordQuasiSymmetricFunctions` or of any associated basis.

        @OPTIONS@

        The ``'words'`` representation of a basis element of
        :class:`WordQuasiSymmetricFunctions`, indexed by an ordered
        set partition `A`, is the packed word associated to `A`.
        See :meth:`OrderedSetPartition.to_packed_word` for details.)

        EXAMPLES::

            sage: WQ = WordQuasiSymmetricFunctions(QQ)
            sage: M = WQ.M()
            sage: elt = M[[[1,2]]]*M[[[1]]]; elt
            M[{1, 2}, {3}] + M[{1, 2, 3}] + M[{3}, {1, 2}]
            sage: M.options.display = "tight"
            sage: elt
            M[{1,2},{3}] + M[{1,2,3}] + M[{3},{1,2}]
            sage: M.options.display = "compact"
            sage: elt
            M[12.3] + M[123] + M[3.12]
            sage: WQ.options._reset()
            sage: M.options.objects = "words"
            sage: elt
            M[1, 1, 2] + M[1, 1, 1] + M[2, 2, 1]
            sage: M.options.display = "tight"
            sage: elt
            M[1,1,2] + M[1,1,1] + M[2,2,1]
            sage: WQ.options.display = "compact"
            sage: elt
            M[112] + M[111] + M[221]
            sage: M.options._reset()
            sage: M.options.objects = "forests"
            sage: elt
            sage: WQ.options.display = "ascii_art"
            sage: elt

            sage: ascii_art(elt)
            sage: M.options._reset()
            sage: elt
            M[{1, 2}, {3}] + M[{1, 2, 3}] + M[{3}, {1, 2}]
        """
        NAME = 'WordQuasiSymmetricFunctions element'
        module = 'sage.combinat.chas.wqsym'
        option_class = 'WordQuasiSymmetricFunctions'
        objects = dict(default="compositions",
                       description='Specifies how basis elements of WordQuasiSymmetricFunctions should be indexed',
                       values=dict(compositions="Indexing the basis by ordered set partitions",
                                   words="Indexing the basis by packed words",
                                   forests="Indexing the basis by decorated forests"),
                                   case_sensitive=False)
        display = dict(default="normal",
                       description='Specifies how basis elements of WordQuasiSymmetricFunctions should be printed',
                       values=dict(normal="Using the normal representation",
                                   tight="Dropping spaces after commas",
                                   compact="Using a severely compacted representation",
                                   ascii_art="Using the ascii art representation"),
                                   case_sensitive=False)


    class Monomial(WQSymBasis_abstract):
        r"""
        The Monomial basis of `WQSym`.

        The family `(\mathbf{M}_u)`, as defined in
        :class:`~sage.combinat.chas.wqsym.WordQuasiSymmetricFunctions`
        with `u` ranging over all packed words, is a basis for the
        free `R`-module `WQSym` and called the *Monomial basis*.
        Here it is labelled using ordered set partitions.

        EXAMPLES::

            sage: WQSym = algebras.WQSym(QQ)
            sage: WQSym.M()
            Word Quasi-symmetric functions over Rational Field in the Monomial basis
        """
        _prefix = "M"
        _basis_name = "Monomial"

        def product_on_basis(self, x, y):
            r"""
            Return the (associative) `*` product of the basis elements
            of ``self`` indexed by the ordered set partitions `x` and
            `y`.

            This is the shifted quasi-shuffle product of `x` and `y`.

            EXAMPLES::

                sage: A = algebras.WQSym(QQ).M()
                sage: x = OrderedSetPartition([[1],[2,3]])
                sage: y = OrderedSetPartition([[1,2]])
                sage: z = OrderedSetPartition([[1,2],[3]])
                sage: A.product_on_basis(x, y)
                M[{1}, {2, 3}, {4, 5}] + M[{1}, {2, 3, 4, 5}]
                 + M[{1}, {4, 5}, {2, 3}] + M[{1, 4, 5}, {2, 3}]
                 + M[{4, 5}, {1}, {2, 3}]
                sage: A.product_on_basis(x, z)
                M[{1}, {2, 3}, {4, 5}, {6}] + M[{1}, {2, 3, 4, 5}, {6}]
                 + M[{1}, {4, 5}, {2, 3}, {6}] + M[{1}, {4, 5}, {2, 3, 6}]
                 + M[{1}, {4, 5}, {6}, {2, 3}] + M[{1, 4, 5}, {2, 3}, {6}]
                 + M[{1, 4, 5}, {2, 3, 6}] + M[{1, 4, 5}, {6}, {2, 3}]
                 + M[{4, 5}, {1}, {2, 3}, {6}] + M[{4, 5}, {1}, {2, 3, 6}]
                 + M[{4, 5}, {1}, {6}, {2, 3}] + M[{4, 5}, {1, 6}, {2, 3}]
                 + M[{4, 5}, {6}, {1}, {2, 3}]
                sage: A.product_on_basis(y, y)
                M[{1, 2}, {3, 4}] + M[{1, 2, 3, 4}] + M[{3, 4}, {1, 2}]

            TESTS::

                sage: one = OrderedSetPartition([])
                sage: all(A.product_on_basis(one, z) == A(z) == A.basis()[z] for z in OrderedSetPartitions(3))
                True
                sage: all(A.product_on_basis(z, one) == A(z) == A.basis()[z] for z in OrderedSetPartitions(3))
                True
            """
            K = self.basis().keys()
            if not x:
                return self.monomial(y)
            m = max(max(part) for part in x)  # The degree of x
            x = [set(part) for part in x]
            yshift = [[val + m for val in part] for part in y]

            def union(X, Y):
                return X.union(Y)
            return self.sum_of_monomials(ShuffleProduct_overlapping(x, yshift,
                                                                    K, union))

        def coproduct_on_basis(self, x):
            r"""
            Return the coproduct of ``self`` on the basis element
            indexed by the ordered set partition ``x``.

            EXAMPLES::

                sage: M = algebras.WQSym(QQ).M()

                sage: M.coproduct(M.one())  # indirect doctest
                M[] # M[]
                sage: M.coproduct( M([[1]]) )  # indirect doctest
                M[] # M[{1}] + M[{1}] # M[]
                sage: M.coproduct( M([[1,2]]) )
                M[] # M[{1, 2}] + M[{1, 2}] # M[]
                sage: M.coproduct( M([[1], [2]]) )
                M[] # M[{1}, {2}] + M[{1}] # M[{1}] + M[{1}, {2}] # M[]
            """
            if not len(x):
                return self.one().tensor(self.one())
            K = self.indices()

            def standardize(P):  # standardize an ordered set partition
                base = sorted(sum((list(part) for part in P), []))
                # base is the ground set of P, as a sorted list.
                d = {val: i + 1 for i, val in enumerate(base)}
                # d is the unique order isomorphism from base to
                # {1, 2, ..., |base|} (encoded as dict).
                return K([[d[x] for x in part] for part in P])
            T = self.tensor_square()
            return T.sum_of_monomials((standardize(x[:i]), standardize(x[i:]))
                                      for i in range(len(x) + 1))

    M = Monomial


    class Characteristic(WQSymBasis_abstract):
        r"""
        The Characteristic basis of `WQSym`.

        The *Characteristic basis* is a graded basis `(X_P)` of `WQSym`,
        indexed by ordered set partitions `P`. It is defined by

        .. MATH::

            X_P = (-1)^{\ell(P)} \mathbf{M}_P ,

        where `(\mathbf{M}_P)_P` denotes the Monomial basis,
        and where `\ell(P)` denotes the number of blocks in an ordered
        set partition `P`.

        EXAMPLES::

            sage: WQSym = algebras.WQSym(QQ)
            sage: X = WQSym.X(); X
            Word Quasi-symmetric functions over Rational Field in the Characteristic basis

            sage: X[[[1,2,3]]] * X[[1,2],[3]]
            X[{1, 2, 3}, {4, 5}, {6}] - X[{1, 2, 3, 4, 5}, {6}]
             + X[{4, 5}, {1, 2, 3}, {6}] - X[{4, 5}, {1, 2, 3, 6}]
             + X[{4, 5}, {6}, {1, 2, 3}]

            sage: X[[1, 4], [3], [2]].coproduct()
            X[] # X[{1, 4}, {3}, {2}] + X[{1, 2}] # X[{2}, {1}]
             + X[{1, 3}, {2}] # X[{1}] + X[{1, 4}, {3}, {2}] # X[]

            sage: M = WQSym.M()
            sage: M(X[[1, 2, 3],])
            -M[{1, 2, 3}]
            sage: M(X[[1, 3], [2]])
            M[{1, 3}, {2}]
            sage: X(M[[1, 2, 3],])
            -X[{1, 2, 3}]
            sage: X(M[[1, 3], [2]])
            X[{1, 3}, {2}]
        """
        _prefix = "X"
        _basis_name = "Characteristic"

        def __init__(self, alg):
            """
            Initialize ``self``.

            EXAMPLES::

                sage: X = algebras.WQSym(QQ).X()
                sage: TestSuite(X).run()  # long time
            """
            WQSymBasis_abstract.__init__(self, alg)

            M = self.realization_of().M()
            mone = -self.base_ring().one()

            def sgn(P):
                return mone**len(P)
            self.module_morphism(codomain=M, diagonal=sgn).register_as_coercion()
            M.module_morphism(codomain=self, diagonal=sgn).register_as_coercion()

        class Element(WQSymBasis_abstract.Element):
            def algebraic_complement(self):
                r"""
                Return the image of the element ``self`` of `WQSym`
                under the algebraic complement involution.

                See
                :meth:`WQSymBases.ElementMethods.algebraic_complement`
                for a definition of the involution and for examples.

                .. SEEALSO::

                    :meth:`coalgebraic_complement`, :meth:`star_involution`

                EXAMPLES::

                    sage: WQSym = algebras.WQSym(ZZ)
                    sage: X = WQSym.X()
                    sage: X[[1,2],[5,6],[3,4]].algebraic_complement()
                    X[{3, 4}, {5, 6}, {1, 2}]
                    sage: X[[3], [1, 2], [4]].algebraic_complement()
                    X[{4}, {1, 2}, {3}]

                TESTS::

                    sage: M = WQSym.M()
                    sage: all(M(X[A]).algebraic_complement() == M(X[A].algebraic_complement())
                    ....:     for A in OrderedSetPartitions(4))
                    True
                """
                # See the WQSymBases.ElementMethods.algebraic_complement doc
                # for the formula we're using here.
                Q = self.parent()
                OSPs = Q.basis().keys()
                return Q._from_dict({OSPs(A.reversed()): c for (A, c) in self},
                                    remove_zeros=False)

            def coalgebraic_complement(self):
                r"""
                Return the image of the element ``self`` of `WQSym`
                under the coalgebraic complement involution.

                See
                :meth:`WQSymBases.ElementMethods.coalgebraic_complement`
                for a definition of the involution and for examples.

                .. SEEALSO::

                    :meth:`algebraic_complement`, :meth:`star_involution`

                EXAMPLES::

                    sage: WQSym = algebras.WQSym(ZZ)
                    sage: X = WQSym.X()
                    sage: X[[1,2],[5,6],[3,4]].coalgebraic_complement()
                    X[{5, 6}, {1, 2}, {3, 4}]
                    sage: X[[3], [1, 2], [4]].coalgebraic_complement()
                    X[{2}, {3, 4}, {1}]

                TESTS::

                    sage: M = WQSym.M()
                    sage: all(M(X[A]).coalgebraic_complement()
                    ....:     == M(X[A].coalgebraic_complement())
                    ....:     for A in OrderedSetPartitions(4))
                    True
                """
                # See the WQSymBases.ElementMethods.coalgebraic_complement doc
                # for the formula we're using here.
                Q = self.parent()
                OSPs = Q.basis().keys()
                return Q._from_dict({OSPs(A.complement()): c for (A, c) in self},
                                    remove_zeros=False)

            def star_involution(self):
                r"""
                Return the image of the element ``self`` of `WQSym`
                under the star involution.

                See
                :meth:`WQSymBases.ElementMethods.star_involution`
                for a definition of the involution and for examples.

                .. SEEALSO::

                    :meth:`algebraic_complement`, :meth:`coalgebraic_complement`

                EXAMPLES::

                    sage: WQSym = algebras.WQSym(ZZ)
                    sage: X = WQSym.X()
                    sage: X[[1,2],[5,6],[3,4]].star_involution()
                    X[{3, 4}, {1, 2}, {5, 6}]
                    sage: X[[3], [1, 2], [4]].star_involution()
                    X[{1}, {3, 4}, {2}]

                TESTS:

                    sage: M = WQSym.M()
                    sage: all(M(X[A]).star_involution() == M(X[A].star_involution())
                    ....:     for A in OrderedSetPartitions(4))
                    True
                """
                # See the WQSymBases.ElementMethods.star_involution doc
                # for the formula we're using here.
                Q = self.parent()
                OSPs = Q.basis().keys()
                return Q._from_dict({OSPs(A.complement().reversed()): c for (A, c) in self},
                                    remove_zeros=False)

    X = Characteristic

    class Cone(WQSymBasis_abstract):
        r"""
        The Cone basis of `WQSym`.

        Let `(X_P)_P` denote the Characteristic basis of `WQSym`.
        Denote the quasi-shuffle of two ordered set partitions `A` and
        `B` by `A \Box B`. For an ordered set partition
        `P = (P_1, \ldots, P_{\ell})`, we form a list of ordered set
        partitions `[P] := (P'_1, \ldots, P'_k)` as follows.
        Define a strictly decreasing sequence of integers
        `\ell + 1 = i_0 > i_1 > \cdots > i_k = 1` recursively by
        requiring that `\min P_{i_j} \leq \min P_a` for all `a < i_{j-1}`.
        Set `P'_j = (P_{i_j}, \ldots, P_{i_{j-1}-1})`.

        The *Cone basis* `(C_P)_P` is defined by

        .. MATH::

            C_P = \sum_Q X_Q,

        where the sum is over all elements `Q` of the quasi-shuffle
        product `P'_1 \Box P'_2 \Box \cdots \Box P'_k` with
        `[P] = (P'_1, \ldots, P'_k)`.

        EXAMPLES::

            sage: WQSym = algebras.WQSym(QQ)
            sage: C = WQSym.C()
            sage: C
            Word Quasi-symmetric functions over Rational Field in the Cone basis

            sage: X = WQSym.X()
            sage: X(C[[2,3],[1,4]])
            X[{1, 2, 3, 4}] + X[{1, 4}, {2, 3}] + X[{2, 3}, {1, 4}]
            sage: X(C[[1,4],[2,3]])
            X[{1, 4}, {2, 3}]
            sage: X(C[[2,3],[1],[4]])
            X[{1}, {2, 3}, {4}] + X[{1}, {2, 3, 4}] + X[{1}, {4}, {2, 3}]
             + X[{1, 2, 3}, {4}] + X[{2, 3}, {1}, {4}]
            sage: X(C[[3], [2, 5], [1, 4]])
            X[{1, 2, 3, 4, 5}] + X[{1, 2, 4, 5}, {3}] + X[{1, 3, 4}, {2, 5}]
             + X[{1, 4}, {2, 3, 5}] + X[{1, 4}, {2, 5}, {3}]
             + X[{1, 4}, {3}, {2, 5}] + X[{2, 3, 5}, {1, 4}]
             + X[{2, 5}, {1, 3, 4}] + X[{2, 5}, {1, 4}, {3}]
             + X[{2, 5}, {3}, {1, 4}] + X[{3}, {1, 2, 4, 5}]
             + X[{3}, {1, 4}, {2, 5}] + X[{3}, {2, 5}, {1, 4}]
            sage: C(X[[2,3],[1,4]])
            -C[{1, 2, 3, 4}] - C[{1, 4}, {2, 3}] + C[{2, 3}, {1, 4}]

        REFERENCES:

        - Section 4 of [Early2017]_

        .. TODO::

            Experiments suggest that :meth:`algebraic_complement`,
            :meth:`coalgebraic_complement`, and :meth:`star_involution`
            should have reasonable formulas on the C basis; at least
            the coefficients of the outputs on any element of the C
            basis seem to be always `0, 1, -1`.
            Is this true? What is the formula?
        """
        _prefix = "C"
        _basis_name = "Cone"

        def __init__(self, alg):
            """
            Initialize ``self``.

            EXAMPLES::

                sage: C = algebras.WQSym(QQ).C()
                sage: TestSuite(C).run()  # long time
            """
            WQSymBasis_abstract.__init__(self, alg)

            X = self.realization_of().X()
            phi = self.module_morphism(self._C_to_X, codomain=X, unitriangular="upper")
            phi.register_as_coercion()
            inv_phi = ~phi
            inv_phi.register_as_coercion()
            # We need to explicitly construct the coercion to/from M via X
            #   as otherwise, when another basis B is created before X, the
            #   coercion is attempted to be built via B, which is cannot do.
            #   So the coercion map returned is the default one that calls
            #   the _element_constructor_.
            #   This is only a problem because X is not the default
            #   a_realization(), which is M, and the coercions are always
            #   first attempted through M to another basis. -- TS
            M = self.realization_of().M()
            M.register_coercion(M.coerce_map_from(X) * phi)
            self.register_coercion(inv_phi * X.coerce_map_from(M))

        def some_elements(self):
            """
            Return some elements of the word quasi-symmetric functions
            in the Cone basis.

            EXAMPLES::

                sage: C = algebras.WQSym(QQ).C()
                sage: C.some_elements()
                [C[], C[{1}], C[{1, 2}], C[] + 1/2*C[{1}]]
            """
            u = self.one()
            o = self([[1]])
            s = self.base_ring().an_element()
            return [u, o, self([[1,2]]), u + s*o]

        def _C_to_X(self, P):
            """
            Return the image of the basis element of ``self`` indexed
            by ``P`` in the Characteristic basis.

            EXAMPLES::

                sage: C = algebras.WQSym(QQ).C()
                sage: OSP = C.basis().keys()
                sage: C._C_to_X(OSP([[2,3],[1,4]]))
                X[{1, 2, 3, 4}] + X[{1, 4}, {2, 3}] + X[{2, 3}, {1, 4}]
            """
            X = self.realization_of().X()
            if not P:
                return X.one()

            OSP = self.basis().keys()

            # Convert to standard set of ordered set partitions
            temp = list(P)
            data = []
            while temp:
                i = min(min(X) for X in temp)
                for j,A in enumerate(temp):
                    if i in A:
                        data.append(OSP(temp[j:]))
                        temp = temp[:j]
                        break

            # Perform the quasi-shuffle product
            cur = {data[0]: 1}
            for B in data[1:]:
                ret = {}
                for A in cur:
                    for C in ShuffleProduct_overlapping(A, B, element_constructor=OSP):
                        if C in ret:
                            ret[C] += cur[A]
                        else:
                            ret[C] = cur[A]
                cur = ret

            # Return the result in the X basis
            return X._from_dict(cur, coerce=True)

    C = Cone

    class StronglyCoarser(WQSymBasis_abstract):
        r"""
        The Q basis of `WQSym`.

        We define a partial order `\leq` on the set of all ordered
        set partitions as follows: `A \leq B` if and only if
        `A` is strongly finer than `B` (see
        :meth:`~sage.combinat.set_partition_ordered.OrderedSetPartition.is_strongly_finer`
        for a definition of this).

        The *Q basis* `(Q_P)_P` is a basis of `WQSym` indexed by ordered
        set partitions, and is defined by

        .. MATH::

            Q_P = \sum \mathbf{M}_W,

        where the sum is over ordered set partitions `W` satisfying
        `P \leq W`.

        EXAMPLES::

            sage: WQSym = algebras.WQSym(QQ)
            sage: M = WQSym.M(); Q = WQSym.Q()
            sage: Q
            Word Quasi-symmetric functions over Rational Field in the Q basis

            sage: Q(M[[2,3],[1,4]])
            Q[{2, 3}, {1, 4}]
            sage: Q(M[[1,2],[3,4]])
            Q[{1, 2}, {3, 4}] - Q[{1, 2, 3, 4}]
            sage: M(Q[[1,2],[3,4]])
            M[{1, 2}, {3, 4}] + M[{1, 2, 3, 4}]
            sage: M(Q[[2,3],[1],[4]])
            M[{2, 3}, {1}, {4}] + M[{2, 3}, {1, 4}]
            sage: M(Q[[3], [2, 5], [1, 4]])
            M[{3}, {2, 5}, {1, 4}]
            sage: M(Q[[1, 4], [2, 3], [5], [6]])
            M[{1, 4}, {2, 3}, {5}, {6}] + M[{1, 4}, {2, 3}, {5, 6}]
             + M[{1, 4}, {2, 3, 5}, {6}] + M[{1, 4}, {2, 3, 5, 6}]

            sage: Q[[1, 3], [2]] * Q[[1], [2]]
            Q[{1, 3}, {2}, {4}, {5}] + Q[{1, 3}, {4}, {2}, {5}]
             + Q[{1, 3}, {4}, {5}, {2}] + Q[{4}, {1, 3}, {2}, {5}]
             + Q[{4}, {1, 3}, {5}, {2}] + Q[{4}, {5}, {1, 3}, {2}]

            sage: Q[[1, 3], [2]].coproduct()
            Q[] # Q[{1, 3}, {2}] + Q[{1, 2}] # Q[{1}] + Q[{1, 3}, {2}] # Q[]

        REFERENCES:

        - Section 6 of [BerZab05]_
        """
        _prefix = "Q"
        _basis_name = "Q"

        def __init__(self, alg):
            """
            Initialize ``self``.

            EXAMPLES::

                sage: Q = algebras.WQSym(QQ).Q()
                sage: TestSuite(Q).run()  # long time
            """
            WQSymBasis_abstract.__init__(self, alg)

            M = self.realization_of().M()
            phi = self.module_morphism(self._Q_to_M, codomain=M, unitriangular="lower")
            phi.register_as_coercion()
            phi_inv = M.module_morphism(self._M_to_Q, codomain=self, unitriangular="lower")
            phi_inv.register_as_coercion()

        def some_elements(self):
            """
            Return some elements of the word quasi-symmetric functions
            in the Q basis.

            EXAMPLES::

                sage: Q = algebras.WQSym(QQ).Q()
                sage: Q.some_elements()
                [Q[], Q[{1}], Q[{1, 2}], Q[] + 1/2*Q[{1}]]
            """
            u = self.one()
            o = self([[1]])
            s = self.base_ring().an_element()
            return [u, o, self([[1,2]]), u + s*o]

        def _Q_to_M(self, P):
            """
            Return the image of the basis element of ``self`` indexed
            by ``P`` in the Monomial basis.

            EXAMPLES::

                sage: Q = algebras.WQSym(QQ).Q()
                sage: OSP = Q.basis().keys()
                sage: Q._Q_to_M(OSP([[2,3],[1,4]]))
                M[{2, 3}, {1, 4}]
                sage: Q._Q_to_M(OSP([[1,2],[3,4]]))
                M[{1, 2}, {3, 4}] + M[{1, 2, 3, 4}]
            """
            M = self.realization_of().M()
            if not P:
                return M.one()

            OSP = self.basis().keys()
            R = M.base_ring()
            one = R.one()
            return M._from_dict({OSP(G): one for G in P.strongly_fatter()},
                                coerce=False)

        def _M_to_Q(self, P):
            """
            Return the image of the basis element of the monomial
            basis indexed by ``P`` in the Q basis ``self``.

            EXAMPLES::

                sage: Q = algebras.WQSym(QQ).Q()
                sage: M = algebras.WQSym(QQ).M()
                sage: OSP = Q.basis().keys()
                sage: Q._M_to_Q(OSP([[2,3],[1,4]]))
                Q[{2, 3}, {1, 4}]
                sage: Q._M_to_Q(OSP([[1,2],[3,4]]))
                Q[{1, 2}, {3, 4}] - Q[{1, 2, 3, 4}]

            TESTS::

                sage: Q = algebras.WQSym(QQ).Q()
                sage: M = algebras.WQSym(QQ).M()
                sage: OSP4 = OrderedSetPartitions(4)
                sage: all(M(Q(M[P])) == M[P] for P in OSP4) # long time
                True
                sage: all(Q(M(Q[P])) == Q[P] for P in OSP4) # long time
                True
            """
            Q = self
            if not P:
                return Q.one()

            OSP = self.basis().keys()
            R = self.base_ring()
            one = R.one()
            lenP = len(P)

            def sign(R):
                # the coefficient with which another
                # ordered set partition will appear
                if len(R) % 2 == lenP % 2:
                    return one
                return -one
            return Q._from_dict({OSP(G): sign(G) for G in P.strongly_fatter()},
                                coerce=False)

        def product_on_basis(self, x, y):
            r"""
            Return the (associative) `*` product of the basis elements
            of the Q basis ``self`` indexed by the ordered set partitions
            `x` and `y`.

            This is the shifted shuffle product of `x` and `y`.

            EXAMPLES::

                sage: A = algebras.WQSym(QQ).Q()
                sage: x = OrderedSetPartition([[1],[2,3]])
                sage: y = OrderedSetPartition([[1,2]])
                sage: z = OrderedSetPartition([[1,2],[3]])
                sage: A.product_on_basis(x, y)
                Q[{1}, {2, 3}, {4, 5}] + Q[{1}, {4, 5}, {2, 3}]
                 + Q[{4, 5}, {1}, {2, 3}]
                sage: A.product_on_basis(x, z)
                Q[{1}, {2, 3}, {4, 5}, {6}] + Q[{1}, {4, 5}, {2, 3}, {6}]
                 + Q[{1}, {4, 5}, {6}, {2, 3}] + Q[{4, 5}, {1}, {2, 3}, {6}]
                 + Q[{4, 5}, {1}, {6}, {2, 3}] + Q[{4, 5}, {6}, {1}, {2, 3}]
                sage: A.product_on_basis(y, y)
                Q[{1, 2}, {3, 4}] + Q[{3, 4}, {1, 2}]

            TESTS::

                sage: one = OrderedSetPartition([])
                sage: all(A.product_on_basis(one, z) == A(z) == A.basis()[z] for z in OrderedSetPartitions(3))
                True
                sage: all(A.product_on_basis(z, one) == A(z) == A.basis()[z] for z in OrderedSetPartitions(3))
                True
            """
            K = self.basis().keys()
            if not x:
                return self.monomial(y)
            m = max(max(part) for part in x)  # The degree of x
            x = [set(part) for part in x]
            yshift = [[val + m for val in part] for part in y]

            def union(X, Y):
                return X.union(Y)
            return self.sum_of_monomials(ShuffleProduct(x, yshift, K))

        def coproduct_on_basis(self, x):
            r"""
            Return the coproduct of ``self`` on the basis element
            indexed by the ordered set partition ``x``.

            EXAMPLES::

                sage: Q = algebras.WQSym(QQ).Q()

                sage: Q.coproduct(Q.one())  # indirect doctest
                Q[] # Q[]
                sage: Q.coproduct( Q([[1]]) )  # indirect doctest
                Q[] # Q[{1}] + Q[{1}] # Q[]
                sage: Q.coproduct( Q([[1,2]]) )
                Q[] # Q[{1, 2}] + Q[{1, 2}] # Q[]
                sage: Q.coproduct( Q([[1], [2]]) )
                Q[] # Q[{1}, {2}] + Q[{1}] # Q[{1}] + Q[{1}, {2}] # Q[]
                sage: Q[[1,2],[3],[4]].coproduct()
                Q[] # Q[{1, 2}, {3}, {4}] + Q[{1, 2}] # Q[{1}, {2}]
                 + Q[{1, 2}, {3}] # Q[{1}] + Q[{1, 2}, {3}, {4}] # Q[]
            """
            # The coproduct on the Q basis satisfies the same formula
            # as on the M basis. This is easily derived from the
            # formula on the M basis.
            if not len(x):
                return self.one().tensor(self.one())
            K = self.indices()

            def standardize(P):  # standardize an ordered set partition
                base = sorted(sum((list(part) for part in P), []))
                # base is the ground set of P, as a sorted list.
                d = {val: i + 1 for i, val in enumerate(base)}
                # d is the unique order isomorphism from base to
                # {1, 2, ..., |base|} (encoded as dict).
                return K([[d[x] for x in part] for part in P])
            T = self.tensor_square()
            return T.sum_of_monomials((standardize(x[:i]), standardize(x[i:]))
                                      for i in range(len(x) + 1))

        
        def left_product_on_basis(self, x, y):
            '''
            TESTS::

                sage: WQSym = algebras.WQSym(QQ)
                sage: OSP = OrderedSetPartition
                sage: Q = WQSym.Q()
                sage: Q.options.objects = 'words'
                sage: Q.left_product_on_basis(OSP([1,2]),OSP([1]))
                Q[2, 3, 1] + Q[1, 3, 2]
                sage: Q.left_product_on_basis(OSP([]),OSP([]))
                0
                sage: Q.left_product_on_basis(OSP([2,1]),OSP([]))
                Q[2, 1]
                sage: Q.left_product_on_basis(OSP([]),OSP([1]))
                0
                sage: Q[1,2]<<Q[1]
                Q[2, 3, 1] + Q[1, 3, 2]
                sage: Q.left_product_on_basis(OSP([2,1,2]),OSP([2,1]))
                Q[4, 3, 4, 2, 1] + Q[4, 2, 4, 3, 1] + Q[4, 1, 4, 3, 2]
                sage: Q[2,1,2]<<Q[2,1]
                Q[4, 3, 4, 2, 1] + Q[4, 2, 4, 3, 1] + Q[4, 1, 4, 3, 2]
                sage: Q[1]<<(Q[1]>>Q[1])
                Q[3, 1, 2]
                sage: Q[1]<<(Q[1]>>(Q[1]*Q[1]))
                Q[4, 2, 3, 1] + Q[4, 1, 3, 2] + Q[4, 2, 1, 3] + Q[4, 1, 2, 3]
            '''
            if not x:
                return self(self.base_ring().zero())
            if not y:
                return self.monomial(OrderedSetPartition(x))
            
            # x = PackedWord(OrderedSetPartition(x).to_packed_word())
            m = x.size()
            yshift = [{i + m for i in s} for s in y]
            SP = ShuffleProduct(x[:-1], yshift, list)
            SP = [OrderedSetPartition(osp+[x[-1]]) for osp in SP]
            return self.sum_of_monomials(SP)


        def right_product_on_basis(self, x, y):
            '''
            TESTS::

                sage: WQSym = algebras.WQSym(QQ)
                sage: OSP = OrderedSetPartition
                sage: Q = WQSym.Q()
                sage: Q.options.objects = 'words'
                sage: Q.right_product_on_basis(OSP([1,2]),OSP([1]))
                Q[1, 2, 3]
                sage: Q.right_product_on_basis(OSP([]),OSP([]))
                0
                sage: Q.right_product_on_basis(OSP([2,1]),OSP([]))
                0
                sage: Q.right_product_on_basis(OSP([]),OSP([1]))
                Q[1]
                sage: Q.right_product_on_basis(OSP([1,2]),OSP([1]))
                Q[1, 2, 3]
                sage: Q[1,2]>>Q[1]
                Q[1, 2, 3]
                sage: Q.right_product_on_basis(OSP([2,1,2]),OSP([2,1]))
                Q[3, 1, 3, 4, 2] + Q[3, 2, 3, 4, 1] + Q[2, 1, 2, 4, 3]
                sage: Q[2,1,2]>>Q[2,1]
                Q[3, 1, 3, 4, 2] + Q[3, 2, 3, 4, 1] + Q[2, 1, 2, 4, 3]
                sage: Q[1]<<(Q[1]>>Q[1])
                Q[3, 1, 2]
                sage: Q[1]<<(Q[1]>>(Q[1]*Q[1]))
                Q[4, 2, 3, 1] + Q[4, 1, 3, 2] + Q[4, 2, 1, 3] + Q[4, 1, 2, 3]
            '''
            if not y:
                return self(self.base_ring().zero())
            if not x:
                return self.monomial(OrderedSetPartition(y))
            
            # x = PackedWord(OrderedSetPartition(x).to_packed_word())
            m = x.size()
            yshift = [{i + m for i in s} for s in y]
            SP = ShuffleProduct(x, yshift[:-1], list)
            SP = [OrderedSetPartition(osp+[yshift[-1]]) for osp in SP]
            return self.sum_of_monomials(SP)

        def left_coproduct_on_basis(self, osp):
            '''
            TESTS::

                sage: WQSym = algebras.WQSym(QQ)
                sage: OSP = OrderedSetPartition
                sage: Q = WQSym.Q()
                sage: Q.options.objects = 'words'
                sage: Q.left_coproduct_on_basis(OSP([1,2]))
                0
                sage: Q.left_coproduct_on_basis(OSP([2,1]))
                Q[1] # Q[1]
                sage: Q.left_coproduct_on_basis(OSP([1]))
                0
                sage: Q.left_coproduct_on_basis(OSP([]))
                0
                sage: Q.left_coproduct_on_basis(OSP([1,3,2]))
                Q[1, 2] # Q[1]
                sage: Q.left_coproduct_on_basis(OSP([3,1,2]))
                Q[1, 2] # Q[1]
                sage: Q.left_coproduct_on_basis(OSP([3,1,2,4]))
                0
                sage: Q.left_coproduct_on_basis(OSP([3,1,4,2]))
                Q[1, 2] # Q[1, 2] + Q[3, 1, 2] # Q[1]
                sage: Q.left_coproduct_on_basis(OSP([1,2,2,1]))
                Q[1, 1] # Q[1, 1]
                sage: Q.left_coproduct_on_basis(OSP([1,4,3,4,3,2]))
                Q[1, 2] # Q[2, 1, 2, 1] + Q[1, 3, 3, 2] # Q[1, 1]
                sage: Q.left_coproduct_on_basis(OSP([4,1,4,3,2]))
                Q[1, 2] # Q[2, 2, 1] + Q[1, 3, 2] # Q[1, 1]
            '''
            # pw = PackedWord(OrderedSetPartition(osp).to_packed_word())
            PW = lambda osp : PackedWord(OrderedSetPartition(osp).to_packed_word())
            OSP = lambda l : OrderedSetPartition(l)
            if len(osp) < 2:
                return self(self.base_ring().zero())
            l, r = [], []
            current = l
            for i in osp:
                current.append(i)
                if osp.size() in i:
                    # l = l + r
                    # r = []
                    current = r
            #import pdb; pdb.set_trace()
            return self.tensor_square().sum_of_monomials(
                (OSP(OSP(l + r[:i]).to_packed_word()),\
                 OSP(OSP(r[i:]).to_packed_word()))
                for i in range(len(r))
            )

        def right_coproduct_on_basis(self, osp):
            '''
            TESTS::

                sage: WQSym = algebras.WQSym(QQ)
                sage: OSP = OrderedSetPartition
                sage: Q = WQSym.Q()
                sage: Q.options.objects = 'words'
                sage: Q.right_coproduct_on_basis(OSP([1,2]))
                Q[1] # Q[1]
                sage: Q.right_coproduct_on_basis(OSP([2,1]))
                0
                sage: Q.right_coproduct_on_basis(OSP([1]))
                0
                sage: Q.right_coproduct_on_basis(OSP([]))
                0
                sage: Q.right_coproduct_on_basis(OSP([1,3,2]))
                Q[1] # Q[2, 1]
                sage: Q.right_coproduct_on_basis(OSP([3,1,2]))
                Q[1] # Q[2, 1]
                sage: Q.right_coproduct_on_basis(OSP([3,1,2,4]))
                Q[1] # Q[2, 1, 3] + Q[1, 2] # Q[1, 2] + Q[3, 1, 2] # Q[1]
                sage: Q.right_coproduct_on_basis(OSP([3,1,4,2]))
                Q[1] # Q[2, 3, 1]
                sage: Q.right_coproduct_on_basis(OSP([1,2,2,1]))
                0
                sage: Q.right_coproduct_on_basis(OSP([1,4,3,4,3,2]))
                Q[1] # Q[3, 2, 3, 2, 1]
                sage: Q.right_coproduct_on_basis(OSP([4,1,4,3,2]))
                Q[1] # Q[3, 3, 2, 1]
            '''
            PW = lambda osp : PackedWord(OrderedSetPartition(osp).to_packed_word())
            OSP = lambda l : OrderedSetPartition(l)
            if len(osp) < 2:
                return self(self.base_ring().zero())
            l, r = [], []
            current = l
            for i in osp:
                if osp.size() in i:
                    current = r
                current.append(i)
            return self.tensor_square().sum_of_monomials(
                (OSP(OSP(l[:i + 1]).to_packed_word()),\
                 OSP(OSP(l[i+1:] + r).to_packed_word()))
                for i in range(len(l))
            )

        class Element(WQSymBasis_abstract.Element):
            def algebraic_complement(self):
                r"""
                Return the image of the element ``self`` of `WQSym`
                under the algebraic complement involution.

                See
                :meth:`WQSymBases.ElementMethods.algebraic_complement`
                for a definition of the involution and for examples.

                .. SEEALSO::

                    :meth:`coalgebraic_complement`, :meth:`star_involution`

                EXAMPLES::

                    sage: WQSym = algebras.WQSym(ZZ)
                    sage: Q = WQSym.Q()
                    sage: Q[[1,2],[5,6],[3,4]].algebraic_complement()
                    Q[{3, 4}, {1, 2, 5, 6}] + Q[{3, 4}, {5, 6}, {1, 2}]
                     - Q[{3, 4, 5, 6}, {1, 2}]
                    sage: Q[[3], [1, 2], [4]].algebraic_complement()
                    Q[{1, 2, 4}, {3}] + Q[{4}, {1, 2}, {3}] - Q[{4}, {1, 2, 3}]

                TESTS::

                    sage: M = WQSym.M()
                    sage: all(M(Q[A]).algebraic_complement()  # long time
                    ....:     == M(Q[A].algebraic_complement())
                    ....:     for A in OrderedSetPartitions(4))
                    True
                """
                # See the WQSymBases.ElementMethods.algebraic_complement doc
                # for the formula we're using here.
                BR = self.base_ring()
                one = BR.one()
                mine = -one
                Q = self.parent()
                OSPs = Q.basis().keys()
                from sage.data_structures.blas_dict import linear_combination

                def img(A):
                    # The image of the basis element Q[A], written as a
                    # dictionary (of its coordinates in the Q-basis).
                    Rs = [Rr.reversed() for Rr in A.strongly_fatter()]
                    return {OSPs(P): (one if (len(R) % 2 == len(P) % 2)
                                      else mine)
                            for R in Rs for P in R.strongly_fatter()}
                return Q._from_dict(linear_combination((img(A), c) for (A, c) in self))

            def coalgebraic_complement(self):
                r"""
                Return the image of the element ``self`` of `WQSym`
                under the coalgebraic complement involution.

                See
                :meth:`WQSymBases.ElementMethods.coalgebraic_complement`
                for a definition of the involution and for examples.

                .. SEEALSO::

                    :meth:`algebraic_complement`, :meth:`star_involution`

                EXAMPLES::

                    sage: WQSym = algebras.WQSym(ZZ)
                    sage: Q = WQSym.Q()
                    sage: Q[[1,2],[5,6],[3,4]].coalgebraic_complement()
                    Q[{1, 2, 5, 6}, {3, 4}] + Q[{5, 6}, {1, 2}, {3, 4}] - Q[{5, 6}, {1, 2, 3, 4}]
                    sage: Q[[3], [1, 2], [4]].coalgebraic_complement()
                    Q[{2}, {1, 3, 4}] + Q[{2}, {3, 4}, {1}] - Q[{2, 3, 4}, {1}]

                TESTS::

                    sage: M = WQSym.M()
                    sage: all(M(Q[A]).coalgebraic_complement()  # long time
                    ....:     == M(Q[A].coalgebraic_complement())
                    ....:     for A in OrderedSetPartitions(4))
                    True
                """
                # See the WQSymBases.ElementMethods.coalgebraic_complement doc
                # for the formula we're using here.
                BR = self.base_ring()
                one = BR.one()
                mine = -one
                Q = self.parent()
                OSPs = Q.basis().keys()
                from sage.data_structures.blas_dict import linear_combination

                def img(A):
                    # The image of the basis element Q[A], written as a
                    # dictionary (of its coordinates in the Q-basis).
                    Rs = [Rr.complement() for Rr in A.strongly_fatter()]
                    return {OSPs(P): (one if (len(R) % 2 == len(P) % 2)
                                      else mine)
                            for R in Rs for P in R.strongly_fatter()}
                return Q._from_dict(linear_combination((img(A), c) for (A, c) in self))

            def star_involution(self):
                r"""
                Return the image of the element ``self`` of `WQSym`
                under the star involution.

                See
                :meth:`WQSymBases.ElementMethods.star_involution`
                for a definition of the involution and for examples.

                .. SEEALSO::

                    :meth:`algebraic_complement`, :meth:`coalgebraic_complement`

                EXAMPLES::

                    sage: WQSym = algebras.WQSym(ZZ)
                    sage: Q = WQSym.Q()
                    sage: Q[[1,2],[5,6],[3,4]].star_involution()
                    Q[{3, 4}, {1, 2}, {5, 6}]
                    sage: Q[[3], [1, 2], [4]].star_involution()
                    Q[{1}, {3, 4}, {2}]

                TESTS::

                    sage: M = WQSym.M()
                    sage: all(M(Q[A]).star_involution() == M(Q[A].star_involution())
                    ....:     for A in OrderedSetPartitions(4))
                    True
                """
                # See the WQSymBases.ElementMethods.star_involution doc
                # for the formula we're using here.
                Q = self.parent()
                OSPs = Q.basis().keys()
                return Q._from_dict({OSPs(A.complement().reversed()): c for (A, c) in self},
                                    remove_zeros=False)

    Q = StronglyCoarser

    ############### HuxoD #############
     
    class PrimitiveLeft(WQSymBasis_abstract):
        r"""
        The basis of Primitives and total primitive elements of `WQSym`.
        """
        _prefix = "O"
        _basis_name = "O"

        def __init__(self, alg):
            """
            Initialize ``self``.

            EXAMPLES::

                sage: O = algebras.WQSym(QQ).O()
                sage: TestSuite(O).run()  # long time
            
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: O.options.objects = 'words'
sage: matr_chgmt_base_osp = lambda X,Y, n: matrix([[Y(X(mu)).coefficient(sigma) for mu in OrderedSetPartitions(n)] for sigma in OrderedSetPartitions(n)])
sage: matr_chgmt_base_osp(O,Q,3)
sage: matr_chgmt_base_osp(Q,O,3)
            """
            WQSymBasis_abstract.__init__(self, alg)
            
            Q = self.realization_of().Q()
            phi = self.module_morphism(self._O_to_Q, codomain=Q)
            phi.register_as_coercion()
            inv_phi = Q.module_morphism(self._Q_to_O, codomain=self)
            inv_phi.register_as_coercion()

            M = self.realization_of().M()
            M.register_coercion(M.coerce_map_from(Q) * phi)
            self.register_coercion(inv_phi * Q.coerce_map_from(M))
            
            
        @cached_method
        def _O_to_Q(self, pw):
            """
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: O.options.objects = 'words'
sage: Q(O[1,3,2])
sage: Q(O[2,1,3])
sage: Q(O[2,2,1])
            """
            Q = self.realization_of().Q()
            if not pw:
                return self.one()
            PW = PackedWords().from_ordered_set_partition(pw)
            f = PW.packed_word_to_labelled_forest_left()
            return Q.labelled_forest_to_Basis(f)

        
        @cached_method
        def matr_chgmt_base_osp(X,Y, n):
            from sage.matrix.constructor import Matrix
            return Matrix([[Y(X(mu)).coefficient(sigma) for mu in OrderedSetPartitions(n)] for sigma in OrderedSetPartitions(n)])
        
        # @cached_method
        def _Q_to_O(self, pw):
            """
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: O.options.objects = 'words'
sage: O(Q[1,3,2])
P[1, 3, 2] + P[2, 3, 1] + P[3, 2, 1]
sage: O(Q[2,1,3])
P[2, 1, 3] + P[3, 1, 2] + P[3, 2, 1]
sage: O(Q[2,2,1])
P[2, 2, 1]
sage: O(Q[2,1])
P[2, 1]

TESTS::

sage: O(Q[1,2])+O(Q[2,1])
P[1, 2] + 2*P[2, 1]
sage: O(Q[1,2]+Q[2,1])
P[1, 2] + 2*P[2, 1]
sage: O(Q[1]*Q[1])
P[1, 2] + 2*P[2, 1]
sage: Q[1]*Q[1]
Q[2, 1] + Q[1, 2]
sage: O(Q[2,1]+Q[1,2])
P[1, 2] + 2*P[2, 1]
sage: Q[1]*Q[1]
Q[2, 1] + Q[1, 2]
sage: O(_)
P[1, 2] + 2*P[2, 1]
            """
            Q = self.realization_of().Q()
            if not pw:
                return self.one()

            # import pdb; pdb.set_trace()
            n = pw.size()
            m = self.matr_chgmt_base_osp(Q,n)**-1
            res = 0
            rank = OrderedSetPartitions(n)(list(pw)).rank()
            for r,c in enumerate(m[:, rank]):
                res += c[0] * self[OrderedSetPartitions(n)[r]]
            return res
        
            WQSymBasis_abstract.__init__(self, alg)
            
        def some_elements(self):
            """
            Return some elements of the word quasi-symmetric functions
            in the Homogeneous basis.

            EXAMPLES::

                sage: H = algebras.WQSym(QQ).H()
                sage: H.some_elements()
                [H[], H[{1}], H[{1, 2}], H[] + 1/2*H[{1}]]
            """
            u = self.one()
            o = self([[1]])
            s = self.base_ring().an_element()
            return [u, o, self([[1,2]]), u + s*o]

    O = PrimitiveLeft

    ######## autre base ##########
    class PrimitiveRight(WQSymBasis_abstract):
        r"""
        The basis of Primitives and total primitive elements of `WQSym` dual.
        """
        _prefix = "P"
        _basis_name = "P"

        def __init__(self, alg):
            """
            Initialize ``self``.

            EXAMPLES::

                sage: P = algebras.WQSym(QQ).P()
                sage: TestSuite(P).run()  # long time
            
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: P.options.objects = 'words'
sage: matr_chgmt_base_osp = lambda X,Y, n: matrix([[Y(X(mu)).coefficient(sigma) for mu in OrderedSetPartitions(n)] for sigma in OrderedSetPartitions(n)])
sage: matr_chgmt_base_osp(P,R,3)
sage: matr_chgmt_base_osp(R,P,3)
            """
            WQSymBasis_abstract.__init__(self, alg)
                        
            O = self.realization_of().O()
            phiOP = O.module_morphism(self._O_to_P, codomain=self)
            phiOP.register_as_coercion()
            phiPO = self.module_morphism(self._P_to_O, codomain=O)
            phiPO.register_as_coercion()

            Q = self.realization_of().Q()
            Q.register_coercion(Q.coerce_map_from(O) * phiPO)
            self.register_coercion(phiOP * O.coerce_map_from(Q))

            M = self.realization_of().M()
            M.register_coercion(M.coerce_map_from(O) * phiPO)
            self.register_coercion(phiOP * O.coerce_map_from(M))
            
        @cached_method
        def _O_to_P(self, pw):
            """
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: O.options.objects = 'words'
sage: P(O[1,3,2])
sage: O(P[1,3,2])
sage: P(O[2,2,1])
sage: O(P[2,2,1])
            sage: n = 3
            sage: for w in PackedWords(n):
            ....:     print(O[w], " -> ", P(O[w]))
            sage: for w in Permutations(n):
            ....:     print(O[w], " -> ", P(O[w]))
            """
            if not pw:
                return self.one()
            PW = PackedWords().from_ordered_set_partition(pw)
            def most_right_graft(f,t):
                weight   = lambda t: len(t.label()[1]) + sum(weight(ti) for ti in t)
                weight_r = lambda t: sum(weight(ti) for ti in t[t.label()[0]:])
                cut = t.label()[0]
                lbl = t.label()[1]
                if lbl[-1] == len(lbl) + weight_r(t):
                    return LabelledOrderedTree([x for x in t]+f,
                                               (cut,lbl[:-1]+[lbl[-1]+sum(weight(t)
                                                                          for t in f)]))
                return LabelledOrderedTree([x for x in
                                            t[:-1]]+[most_right_graft(f,
                                                                      t[-1])], t.label())

            def particular_O_to_P(w):
                assert w.is_particular("left")
                t = w.packed_word_to_labelled_tree()
                left_forest = t[:t.label()[0]]
                left_forest_res = [self._O_to_P(PackedWords().labelled_tree_to_packed_word(t)) for t in left_forest]
                left_forest_res = [PackedWords().from_ordered_set_partition(Posp.support()[0]).packed_word_to_labelled_tree() for Posp in left_forest_res]
                if left_forest_res:
                    r_t = LabelledOrderedTree(t[t.label()[0]:], (0, t.label()[1]))
                    return PackedWords().labelled_tree_to_packed_word(most_right_graft(left_forest_res[::-1], r_t))
                return w

            f = PW.packed_word_to_labelled_forest_left()
            res = []
            for t in f:
                left_forest = t[:t.label()[0]]
                left_forest_res = [self._O_to_P(PackedWords().labelled_tree_to_packed_word_left(t)) for t in left_forest]
                left_forest_res = [PackedWords().from_ordered_set_partition(Posp.support()[0]).packed_word_to_labelled_tree() for Posp in left_forest_res]
                r_t = LabelledOrderedTree([x for x in t[t.label()[0]:]],(0,t.label()[1]))
                r_w = PackedWords().labelled_tree_to_packed_word_left(r_t)
                r_w_res = particular_O_to_P(r_w)
                r_t_res = r_w_res.packed_word_to_labelled_tree()
                res_t = LabelledOrderedTree(left_forest_res+[x for x in r_t_res], (len(left_forest),r_t_res.label()[1]))

                res += [PackedWords().labelled_tree_to_packed_word(res_t)]
                
            
            l_shifted_concat = lambda w1, w2: PackedWord([x+max(w2) for x in w1]+w2.list())
            result = []
            for w in res:
                result = l_shifted_concat(result, w)
            return self[PackedWord(result)]

        def _P_to_O(self,pw):
            O = self.realization_of().O()
            res = self._O_to_P(pw).support()[0]
            return O[res]

        def some_elements(self):
            """
            Return some elements of the word quasi-symmetric functions
            in the Homogeneous basis.

            EXAMPLES::

                sage: H = algebras.WQSym(QQ).H()
                sage: H.some_elements()
                [H[], H[{1}], H[{1, 2}], H[] + 1/2*H[{1}]]
            """
            u = self.one()
            o = self([[1]])
            s = self.base_ring().an_element()
            return [u, o, self([[1,2]]), u + s*o]

    P = PrimitiveRight

    ######## autre base ##########
    class RightWeakOrder(WQSymBasis_abstract):
        r"""
        The Right Weak Order basis of `WQSym`.
        """
        _prefix = "R"
        _basis_name = "RightWeakOrder"

        def __init__(self, alg):
            """
            Initialize ``self``.

            EXAMPLES::

                sage: R = algebras.WQSym(QQ).R()
                sage: TestSuite(R).run()  # long time
            
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: R.options.objects = 'words'
sage: matr_chgmt_base_osp = lambda X,Y, n: matrix([[Y(X(mu)).coefficient(sigma) for mu in OrderedSetPartitions(n)] for sigma in OrderedSetPartitions(n)])
sage: matr_chgmt_base_osp(E,R,3)
sage: matr_chgmt_base_osp(R,E,3)
            """
            WQSymBasis_abstract.__init__(self, alg)
            P = self.realization_of().P()
            phi = P.module_morphism(self._P_to_R, codomain=self)
            phi.register_as_coercion()
            inv_phi = self.module_morphism(self._R_to_P, codomain=P)
            inv_phi.register_as_coercion()


            O = self.realization_of().O()
            O.register_coercion(O.coerce_map_from(P) * P.coerce_map_from(self))
            self.register_coercion(self.coerce_map_from(P) * P.coerce_map_from(O))

            Q = self.realization_of().Q()
            Q.register_coercion(Q.coerce_map_from(P) * P.coerce_map_from(self))
            self.register_coercion(self.coerce_map_from(P) * P.coerce_map_from(Q))

            M = self.realization_of().M()
            M.register_coercion(M.coerce_map_from(P) * P.coerce_map_from(self))
            self.register_coercion(self.coerce_map_from(P) * P.coerce_map_from(M))

#             phi.register_as_coercion()
#             inv_phi = ~phi
#             inv_phi.register_as_coercion()

            
#             H = self.realization_of().H()
#             H.register_coercion(H.coerce_map_from(E) * inv_phi)
#             self.register_coercion(phi * E.coerce_map_from(H))
            
#             Q = self.realization_of().Q()
#             Q.register_coercion(Q.coerce_map_from(E) * inv_phi)
#             self.register_coercion(phi * E.coerce_map_from(Q))
            
#             M = self.realization_of().M()
#             M.register_coercion(M.coerce_map_from(E) * inv_phi)
#             self.register_coercion(phi * E.coerce_map_from(M))

#         @cached_method
#         def _E_to_R(self, P):
#             """
# sage: WQSym = algebras.WQSym(QQ)
# sage: WQSym.inject_shorthands()
# sage: H.options.objects = 'words'
# sage: E(R[1,3,2])
# sage: E(R[2,1,3])
# sage: E(R[2,2,1])


#             """
#             E = self.realization_of().E()
#             if not P:
#                 return self.one()
#             PW = PackedWords().from_ordered_set_partition(P)
#             Ring = self.base_ring()
#             one = Ring.one()
#             return self._from_dict({G.to_ordered_set_partition():
#                                  one for G in PW.right_weak_order_smaller()}, coerce=False)

        
#             WQSymBasis_abstract.__init__(self, alg)
              
        # @cached_method
        def _P_to_R(self, pw):
            """
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: O.options.objects = 'words'
sage: R(P[1,3,2])
R[1, 3, 2] - R[2, 3, 1]
sage: R(P[2,1,3])
-R[1, 3, 2] + R[2, 1, 3] - R[3, 1, 2] + R[2, 3, 1]
sage: R(P[2,2,1])
R[2, 2, 1]
            """
            # import pdb; pdb.set_trace()
            P = self.realization_of().P()
            R = self
            if not pw:
                return R.one()
            PW = PackedWords().from_ordered_set_partition(pw)
            f = PW.packed_word_to_labelled_forest()
            return R.labelled_forest_to_Basis(f)

        @staticmethod
        def matr_chgmt_base_osp(X,Y, n):
            from sage.matrix.constructor import Matrix
            return Matrix([[Y(X(mu)).coefficient(sigma) for mu in OrderedSetPartitions(n)] for sigma in OrderedSetPartitions(n)])
        
        # @cached_method
        def _R_to_P(self, pw):
            """
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: R.options.objects = 'words'
sage: P(R[1,3,2])
P[1, 3, 2] + P[2, 3, 1] + P[3, 2, 1]
sage: P(R[2,1,3])
P[2, 1, 3] + P[3, 1, 2] + P[3, 2, 1]
sage: P(R[2,2,1])
P[2, 2, 1]
sage: P(R[2,1])
P[2, 1]

TESTS::

sage: P(R[1,2])+P(R[2,1])
P[1, 2] + 2*P[2, 1]
sage: P(R[1,2]+R[2,1])
P[1, 2] + 2*P[2, 1]
sage: P(R[1]*R[1])
P[1, 2] + 2*P[2, 1]
sage: R[1]*R[1]
R[2, 1] + R[1, 2]
sage: P(R[2,1]+R[1,2])
P[1, 2] + 2*P[2, 1]
sage: R[1]*R[1]
R[2, 1] + R[1, 2]
sage: P(_)
P[1, 2] + 2*P[2, 1]
            """
            P = self.realization_of().P()
            R = self
            if not pw:
                return P.one()
            n = pw.size()
            m = self.matr_chgmt_base_osp(P,R,n)**-1
            res = 0
            rank = OrderedSetPartitions(n)(list(pw)).rank()
            for r,c in enumerate(m[:, rank]):
                res += c[0] * P[OrderedSetPartitions(n)[r]]
            return res
        

        def some_elements(self):
            """
            Return some elements of the word quasi-symmetric functions
            in the Homogeneous basis.

            EXAMPLES::

                sage: H = algebras.WQSym(QQ).H()
                sage: H.some_elements()
                [H[], H[{1}], H[{1, 2}], H[] + 1/2*H[{1}]]
            """
            u = self.one()
            o = self([[1]])
            s = self.base_ring().an_element()
            return [u, o, self([[1,2]]), u + s*o]

        def product_on_basis(self, x, y):
            r"""
            Return the (associative) `*` product of the basis elements
            of the Elementaire basis ``self`` indexed by the ordered set partitions
            `x` and `y`.

            This is the classical shifted shuffle on pw `x` and `y`.


sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
#sage: R.options.objects = 'words'
sage: R[1,1]*R[1,2]
            """
            K = self.basis().keys()
            if not x:
                return self.monomial(y)
            x = PackedWord(x.to_packed_word())
            m = max(x)
            yshift = [int(val) + m for val in y.to_packed_word()]
            SP = ShuffleProduct(x, yshift, PackedWord)
            SP = [pw.to_ordered_set_partition() for pw in SP]
            return self.sum_of_monomials(SP)

        
        def coproduct_on_basis(self, osp):
            '''
            TESTS::

                sage: WQSym = algebras.WQSym(QQ)
                sage: R = WQSym.R()
                sage: R[[]].coproduct()
                R[] # R[]
                sage: R[1].coproduct()
                R[] # R[1] + R[1] # R[]
                sage: R[1, 2].coproduct()
                R[] # R[1, 2] + R[1] # R[1] + R[1, 2] # R[]
                sage: ( R[1, 2] - R[2, 1] ).coproduct()
                R[] # R[1, 2] - R[] # R[2, 1] + R[1, 2] # R[] - R[2, 1] # R[]
                sage: R[2,1,2,1,3].coproduct()
                R[] # R[2, 1, 2, 1, 3] + R[2, 1, 2, 1] # R[1] + R[2, 1, 2, 1, 3] # R[]
                sage: R[1,4,2,1,3,2].coproduct()
                R[] # R[1, 4, 2, 1, 3, 2] + R[1, 4, 2, 1, 3, 2] # R[]
                sage: R[1,4,1,3,2].coproduct() 
               R[] # R[1, 4, 1, 3, 2] + R[1, 2, 1] # R[2, 1] + R[1, 3, 1, 2] # R[1] + R[1, 4, 1, 3, 2] # R[]
            '''
            pw = PackedWord(osp.to_packed_word())
            return self.tensor_square().sum_of_monomials(
                (OrderedSetPartition(PackedWords().pack(pw[:i])),\
                 OrderedSetPartition(PackedWords().pack(pw[i:])))
                    for i in range(len(pw) + 1)
                    if [pw[:i].count(x)
                        for x in pw[i:]].count(0)==len(pw[i:])
            )

        def left_product_on_basis(self, x, y):
            '''
            TESTS::

                sage: WQSym = algebras.WQSym(QQ)
                sage: R = WQSym.R()
                sage: R.options.objects = 'words'
                sage: R.left_product_on_basis([1,2],[1])
                R[1, 3, 2] + R[3, 1, 2]
                sage: R.left_product_on_basis([],[])
                0
                sage: R.left_product_on_basis([2,1],[])
                R[2, 1]
                sage: R.left_product_on_basis([],[1])
                0
                sage: R.left_product_on_basis([1,2],[1])
                R[1, 3, 2] + R[3, 1, 2]
                sage: R[1,2]<<R[1]
                R[1, 3, 2] + R[3, 1, 2]
                sage: R.left_product_on_basis([2,1,2],[2,1])
                R[2, 1, 4, 3, 2] + R[2, 4, 1, 3, 2] + R[4, 2, 1, 3, 2] + R[2, 4, 3, 1, 2] + R[4, 2, 3, 1, 2] + R[4, 3, 2, 1, 2]
                sage: R[2,1,2]<<R[2,1]
                R[2, 1, 4, 3, 2] + R[2, 4, 1, 3, 2] + R[4, 2, 1, 3, 2] + R[2, 4, 3, 1, 2] + R[4, 2, 3, 1, 2] + R[4, 3, 2, 1, 2]
                sage: R[1]<<(R[1]>>R[1])
                R[2, 3, 1]
                sage: R[1]<<(R[1]>>(R[1]*R[1]))
                R[2, 3, 4, 1] + R[2, 4, 3, 1] + R[3, 2, 4, 1] + R[4, 2, 3, 1]
            '''
            if not x:
                return self(self.base_ring().zero())
            
            x = PackedWord(OrderedSetPartition(x).to_packed_word())
            m = max(x)
            yshift = [int(val) + m for val in OrderedSetPartition(y).to_packed_word()]
            SP = ShuffleProduct(x[:-1], yshift, list)
            SP = [OrderedSetPartition(pw+[x[-1]]) for pw in SP]
            return self.sum_of_monomials(SP)

        def left_concat_on_basis(self, x, y):
            '''
            TESTS::

                sage: WQSym = algebras.WQSym(QQ)
                sage: R = WQSym.R()
                sage: R.options.objects = 'words'
                sage: R.left_concat_on_basis([1,2],[1])
                 R[3, 1, 2]
                sage: R.left_concat_on_basis([],[])
                0
                sage: R.left_concat_on_basis([2,1],[])
                R[2, 1]
                sage: R.left_concat_on_basis([],[1])
                0
                sage: R.left_concat_on_basis([2,1,2],[2,1])
                R[4, 3, 2, 1, 2]
            '''
            if not x:
                return self(self.base_ring().zero())
            
            x = list(PackedWord(OrderedSetPartition(x).to_packed_word()))
            m = max(x)
            yshift = [int(val) + m for val in OrderedSetPartition(y).to_packed_word()]
            C = yshift + x
            C = OrderedSetPartition(C)
            return self.monomial(C)

        def right_product_on_basis(self, x, y):
            '''
            TESTS::

                sage: WQSym = algebras.WQSym(QQ)
                sage: R = WQSym.R()
                sage: R.options.objects = 'words'
                sage: R.right_product_on_basis([1,2],[1])
                R[1, 2, 3]
                sage: R.right_product_on_basis([],[])
                0
                sage: R.right_product_on_basis([2,1],[])
                0
                sage: R.right_product_on_basis([],[1])
                R[1]
                sage: R.right_product_on_basis([1,2],[1])
                R[1, 2, 3]
                sage: R[1,2]>>R[1]
                R[1, 2, 3]
                sage: R.right_product_on_basis([2,1,2],[2,1])
                R[2, 1, 2, 4, 3] + R[2, 1, 4, 2, 3] + R[2, 4, 1, 2, 3] + R[4, 2, 1, 2, 3]
                sage: R[2,1,2]>>R[2,1]
                R[2, 1, 2, 4, 3] + R[2, 1, 4, 2, 3] + R[2, 4, 1, 2, 3] + R[4, 2, 1, 2, 3]
                sage: R[1]<<(R[1]>>R[1])
                R[2, 3, 1]
                sage: R[1]<<(R[1]>>(R[1]*R[1]))
                R[2, 3, 4, 1] + R[2, 4, 3, 1] + R[3, 2, 4, 1] + R[4, 2, 3, 1]
            '''
            if not y:
                return self(self.base_ring().zero())
            if not x:
                return self.monomial(OrderedSetPartition(y))
            x = PackedWord(OrderedSetPartition(x).to_packed_word())
            m = max(x)
            yshift = [int(val) + m for val in OrderedSetPartition(y).to_packed_word()]
            SP = ShuffleProduct(x, yshift[:-1], list)
            SP = [OrderedSetPartition(pw+[yshift[-1]]) for pw in SP]
            return self.sum_of_monomials(SP)

        def left_coproduct_on_basis(self, osp):
            ''' 
            TESTS::

                sage: WQSym = algebras.WQSym(QQ)
                sage: R = WQSym.R()
                sage: R.left_coproduct_on_basis([1,2])
                0
                sage: R.left_coproduct_on_basis([2,1])
                R[1] # R[1]
                sage: R.left_coproduct_on_basis([1])
                0
                sage: R.left_coproduct_on_basis([])
                0
                sage: R.left_coproduct_on_basis([1,3,2])
                R[1, 2] # R[1]
                sage: R.left_coproduct_on_basis([3,1,2])
                R[1] # R[1, 2] + R[2, 1] # R[1]
                sage: R.left_coproduct_on_basis([3,1,2,4])
                0
                sage: R.left_coproduct_on_basis([3,1,4,2])
                R[2, 1, 3] # R[1]
                sage: R.left_coproduct_on_basis([1,2,2,1])
                0
                sage: R.left_coproduct_on_basis([1,4,3,4,3,2])
                R[1, 3, 2, 3, 2] # R[1]
                sage: R.left_coproduct_on_basis([4,1,4,3,2])
                R[2, 1, 2] # R[2, 1] + R[3, 1, 3, 2] # R[1]
            '''
            pw = PackedWord(OrderedSetPartition(osp).to_packed_word())
            if len(pw) < 2:
                return self(self.base_ring().zero())
            l, r = [], []
            current = l
            for i in pw:
                current.append(i)
                if i == max(pw):
                    l = l + r
                    r = []
                    current = r
            return self.tensor_square().sum_of_monomials(
                (OrderedSetPartition(PackedWords().pack(l + r[:i])),\
                 OrderedSetPartition(PackedWords().pack(r[i:])))
                for i in range(len(r))
                if [(l+r[:i]).count(x)
                    for x in r[i:]].count(0)==len(r[i:])
            )

        def right_coproduct_on_basis(self, osp):
            '''
            TESTS::

                sage: R = algebras.WQSym(QQ).R()
                sage: R.right_coproduct_on_basis([])
                0
                sage: R.right_coproduct_on_basis([1])
                0
                sage: R.right_coproduct_on_basis([1,2])
                R[1] # R[1]
                sage: R.right_coproduct_on_basis([2,1])
                0
                sage: R.right_coproduct_on_basis([2,3,1])
                R[1] # R[2, 1]
                sage: R.right_coproduct_on_basis([2,4,3,1])
                R[1] # R[3, 2, 1]
                sage: R.right_coproduct_on_basis([2,4,5,3,1])
                R[1] # R[3, 4, 2, 1] + R[1, 2] # R[3, 2, 1]
                sage: R.right_coproduct_on_basis([5,2,4,3,1])
                0
                sage: R.right_coproduct_on_basis([1,2,2,1])
                0
                sage: R.right_coproduct_on_basis([1,4,3,4,3,2])
                R[1] # R[3, 2, 3, 2, 1]
                sage: R.right_coproduct_on_basis([2,1,4,3,4])
                R[1] # R[1, 3, 2, 3] + R[2, 1] # R[2, 1, 2]
            '''
            pw = PackedWord(OrderedSetPartition(osp).to_packed_word())
            if len(pw) < 2:
                return self(self.base_ring().zero())
            l, r = [], []
            current = l
            for i in pw:
                if i == max(pw):
                    current = r
                current.append(i)
            return self.tensor_square().sum_of_monomials(
                (OrderedSetPartition(PackedWords().pack(l[:i + 1])),\
                 OrderedSetPartition(PackedWords().pack(l[i + 1:] + r)))
                for i in range(len(l))
                if [(l[:i + 1]).count(x)
                    for x in (l[i + 1:] + r)].count(0)==len(l[i + 1:] + r)
            )

    R = RightWeakOrder

######## autre base ##########
    class WeakOrderPrimitiveRight(WQSymBasis_abstract):
        r"""

        """
        _prefix = "WP"
        _basis_name = "WeakOrderPrimitiveRight"

        def __init__(self, alg):
            """
            Initialize ``self``.

            EXAMPLES::

                sage: WP = algebras.WQSym(QQ).WP()
                sage: TestSuite(WP).run()  # long time
            
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: WP.options.objects = 'words'
sage: matr_chgmt_base_osp = lambda X,Y, n: matrix([[Y(X(mu)).coefficient(sigma) for mu in OrderedSetPartitions(n)] for sigma in OrderedSetPartitions(n)])
sage: matr_chgmt_base_osp(WP,R,3)
sage: matr_chgmt_base_osp(R,WP,3)
            """
            WQSymBasis_abstract.__init__(self, alg)
# j'aimerais bien enlever la fct new_rank ici pcq c'est pas utile.... pour l'instant ça marche pas bien...
            @cached_function
            def new_rank(x):
                return (SetPartition(x),x.to_packed_word())

            
            R = self.realization_of().R()
            phi = R.module_morphism(self._R_to_WP, codomain=self, unitriangular="lower", key=new_rank)
            phi.register_as_coercion()
            inv_phi = ~phi
            inv_phi.register_as_coercion()

                        
            # M = self.realization_of().M()
            # M.register_coercion(M.coerce_map_from(R) * inv_phi)
            # self.register_coercion(phi * R.coerce_map_from(M))
            
            # Q = self.realization_of().Q()
            # Q.register_coercion(Q.coerce_map_from(R) * inv_phi)
            # self.register_coercion(phi * R.coerce_map_from(Q))

        @cached_method
        def _R_to_WP(self, osp):
            """
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: H.options.objects = 'words'
sage: R(WP[1,3,2])
sage: R(WP[2,1,3])
sage: R(WP[2,2,1])

TODO c'est pas aussi simple que ça.....
            """
            R = self.realization_of().R()
            if not osp:
                return self.one()
            m = len(osp)
            PW = PackedWords().from_ordered_set_partition(OrderedSetPartition(osp[:-1]))
            Ring = self.base_ring()
            one = Ring.one()
            res = []
            for G in PW.left_weak_order_greater():
                x = G
                for k in osp[-1]:
                    x = x[:k-1]+[m]+x[k-1:]
                res+=[PackedWord(x)]
            return self._from_dict({G.to_ordered_set_partition():
                                    one for G in res}, coerce=False)
        
        def some_elements(self):
            """
            Return some elements of the word quasi-symmetric functions
            in the Homogeneous basis.

            EXAMPLES::

                sage: H = algebras.WQSym(QQ).H()
                sage: H.some_elements()
                [H[], H[{1}], H[{1, 2}], H[] + 1/2*H[{1}]]
            """
            u = self.one()
            o = self([[1]])
            s = self.base_ring().an_element()
            return [u, o, self([[1,2]]), u + s*o]

        # def product_on_basis(self, p1, p2):
        #     """
        #     sage: WQSym = algebras.WQSym(QQ)
        #     sage: WQSym.inject_shorthands()
        #     #sage: H.options.objects = 'words'
        #     sage: P[1,2]*P[1]
        #     """
        #     if not p1:
        #         return self.monomial(p2)
        #     if not p2:
        #         return self.monomial(p1)
        #     R = self.realization_of().R()
        #     Rp1=R(self[p1])
        #     Rp2=R(self[p2])
        #     Rres = Rp1*Rp2
        #     coef = Rres.monomial_coefficients()
        #     from sage.matrix.constructor import Matrix
        #     matr_chgmt_base_osp = lambda X,Y, n: Matrix([[Y(X(mu)).coefficient(sigma) for mu in OrderedSetPartitions(n)] for sigma in OrderedSetPartitions(n)])
        #     m = matr_chgmt_base_osp(self,R,p1.size()+p2.size())**-1
        #     res = 0
        #     for x in coef:
        #         for r,c in enumerate(m[:,x.rank()]):
        #             res+= coef[x]*c[0]*self[OrderedSetPartitions(len(p1)+len(p2))[r]]
        #     return res
            
    WP = WeakOrderPrimitiveRight

######## autre base ##########  

    class GreaterLeft(WQSymBasis_abstract):
        r"""
        The multiplicative basis from Q based on left weak order.
        """
        _prefix = "GL"
        _basis_name = "GL"

        def __init__(self, alg):
            """
            Initialize ``self``.

            EXAMPLES::

                sage: GL = algebras.WQSym(QQ).GL()
                sage: TestSuite(O).run()  # long time
            
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: GL.options.objects = 'words'
sage: matr_chgmt_base_osp = lambda X,Y, n: matrix([[Y(X(mu)).coefficient(sigma) for mu in OrderedSetPartitions(n)] for sigma in OrderedSetPartitions(n)])
sage: matr_chgmt_base_osp(GL,Q,3)
sage: matr_chgmt_base_osp(Q,GL,3)
            """
            WQSymBasis_abstract.__init__(self, alg)
            
            @cached_function
            def new_rank(x):
                return (SetPartition(x),x.to_packed_word())
            
            Q = self.realization_of().Q()
            phi = self.module_morphism(self._GL_to_Q, codomain=Q, unitriangular = "lower", key = new_rank)
            phi.register_as_coercion()
            inv_phi = ~phi
            inv_phi.register_as_coercion()

            M = self.realization_of().M()
            M.register_coercion(M.coerce_map_from(Q) * phi)
            self.register_coercion(inv_phi * Q.coerce_map_from(M))
            
            
        @cached_method
        def _GL_to_Q(self, pw):
            """
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: O.options.objects = 'words'
sage: Q(O[1,3,2])
sage: Q(O[2,1,3])
sage: Q(O[2,2,1])
            """
            Q = self.realization_of().Q()
            if not pw:
                return self.one()
            PW = PackedWords().from_ordered_set_partition(pw)
            PW_GL = PW.left_weak_order_greater()
            R = Q.base_ring()
            one = R.one()
            return Q._from_dict({G.to_ordered_set_partition():
                                 one for G in PW.left_weak_order_greater()}, coerce=False)
        
            WQSymBasis_abstract.__init__(self, alg)
            
        def some_elements(self):
            """
            Return some elements of the word quasi-symmetric functions
            in the Homogeneous basis.

            EXAMPLES::

                sage: H = algebras.WQSym(QQ).H()
                sage: H.some_elements()
                [H[], H[{1}], H[{1, 2}], H[] + 1/2*H[{1}]]
            """
            u = self.one()
            o = self([[1]])
            s = self.base_ring().an_element()
            return [u, o, self([[1,2]]), u + s*o]

        def product_on_basis(self, x, y):
            """
            This is the shifted concatenating product of `x` and `y`.
            """
            K = self.basis().keys()
            if not x:
                return self.monomial(y)
            m = max(max(part) for part in x) # The degree of x
            x = [set(part) for part in x]
            yshift = [[val + m for val in part] for part in y]
            return self.monomial(K(x + yshift))
        
    GL = GreaterLeft
    
######## autre base ##########  

    class SmallerRight(WQSymBasis_abstract):
        r"""
        The multiplicative basis from R based on right weak order.
        """
        _prefix = "SR"
        _basis_name = "SR"

        def __init__(self, alg):
            """
            Initialize ``self``.

            EXAMPLES::

                sage: SR = algebras.WQSym(QQ).SR()
                sage: TestSuite(O).run()  # long time
            
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: SR.options.objects = 'words'
sage: matr_chgmt_base_osp = lambda X,Y, n: matrix([[Y(X(mu)).coefficient(sigma) for mu in OrderedSetPartitions(n)] for sigma in OrderedSetPartitions(n)])
sage: matr_chgmt_base_osp(SR,R,3)
sage: matr_chgmt_base_osp(R,SR,3)
            """
            WQSymBasis_abstract.__init__(self, alg)
            
            @cached_function
            def new_rank(x):
                return (x.to_composition(),x.to_packed_word())
            
            R = self.realization_of().R()
            phi = self.module_morphism(self._SR_to_R, codomain=R, unitriangular = "upper", key = new_rank)
            phi.register_as_coercion()
            inv_phi = ~phi
            inv_phi.register_as_coercion()

            M = self.realization_of().M()
            M.register_coercion(M.coerce_map_from(R) * phi)
            self.register_coercion(inv_phi * R.coerce_map_from(M))
            
            
        @cached_method
        def _SR_to_R(self, pw):
            """
sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
sage: O.options.objects = 'words'
sage: R(O[1,3,2])
sage: R(O[2,1,3])
sage: R(O[2,2,1])
            """
            R = self.realization_of().R()
            if not pw:
                return self.one()
            PW = PackedWords().from_ordered_set_partition(pw)
            Ring = R.base_ring()
            one = Ring.one()
            return R._from_dict({G.to_ordered_set_partition():
                                 one for G in PW.right_weak_order_smaller()}, coerce=False)
        
            WQSymBasis_abstract.__init__(self, alg)
            
        def some_elements(self):
            """
            Return some elements of the word quasi-symmetric functions
            in the Homogeneous basis.

            EXAMPLES::

                sage: H = algebras.WQSym(QQ).H()
                sage: H.some_elements()
                [H[], H[{1}], H[{1, 2}], H[] + 1/2*H[{1}]]
            """
            u = self.one()
            o = self([[1]])
            s = self.base_ring().an_element()
            return [u, o, self([[1,2]]), u + s*o]
        
        def product_on_basis(self, x, y):
            """
            This is the concatenating product of shifted `y` and `x`.
            """
            K = self.basis().keys()
            if not x:
                return self.monomial(y)
            m = max(max(part) for part in y) # The degree of x
            xshift = [[val + m for val in part] for part in x]
            y = [set(part) for part in y]
            return self.monomial(K(xshift + y))
        
    SR = SmallerRight
    
############### HuxoD End #############

    class StronglyFiner(WQSymBasis_abstract):
        r"""
        The Phi basis of `WQSym`.

        We define a partial order `\leq` on the set of all ordered
        set partitions as follows: `A \leq B` if and only if
        `A` is strongly finer than `B` (see
        :meth:`~sage.combinat.set_partition_ordered.OrderedSetPartition.is_strongly_finer`
        for a definition of this).

        The *Phi basis* `(\Phi_P)_P` is a basis of `WQSym` indexed by ordered
        set partitions, and is defined by

        .. MATH::

            \Phi_P = \sum \mathbf{M}_W,

        where the sum is over ordered set partitions `W` satisfying
        `W \leq P`.

        Novelli and Thibon introduced this basis in [NovThi06]_
        Section 2.7.2, and called it the quasi-ribbon basis.
        It later reappeared in [MeNoTh11]_ Section 4.3.2.

        EXAMPLES::

            sage: WQSym = algebras.WQSym(QQ)
            sage: M = WQSym.M(); Phi = WQSym.Phi()
            sage: Phi
            Word Quasi-symmetric functions over Rational Field in the Phi basis

            sage: Phi(M[[2,3],[1,4]])
            Phi[{2}, {3}, {1}, {4}] - Phi[{2}, {3}, {1, 4}]
             - Phi[{2, 3}, {1}, {4}] + Phi[{2, 3}, {1, 4}]
            sage: Phi(M[[1,2],[3,4]])
            Phi[{1}, {2}, {3}, {4}] - Phi[{1}, {2}, {3, 4}]
             - Phi[{1, 2}, {3}, {4}] + Phi[{1, 2}, {3, 4}]
            sage: M(Phi[[1,2],[3,4]])
            M[{1}, {2}, {3}, {4}] + M[{1}, {2}, {3, 4}]
             + M[{1, 2}, {3}, {4}] + M[{1, 2}, {3, 4}]
            sage: M(Phi[[2,3],[1],[4]])
            M[{2}, {3}, {1}, {4}] + M[{2, 3}, {1}, {4}]
            sage: M(Phi[[3], [2, 5], [1, 4]])
            M[{3}, {2}, {5}, {1}, {4}] + M[{3}, {2}, {5}, {1, 4}]
             + M[{3}, {2, 5}, {1}, {4}] + M[{3}, {2, 5}, {1, 4}]
            sage: M(Phi[[1, 4], [2, 3], [5], [6]])
            M[{1}, {4}, {2}, {3}, {5}, {6}] + M[{1}, {4}, {2, 3}, {5}, {6}]
             + M[{1, 4}, {2}, {3}, {5}, {6}] + M[{1, 4}, {2, 3}, {5}, {6}]

            sage: Phi[[1],] * Phi[[1, 3], [2]]
            Phi[{1, 2, 4}, {3}] + Phi[{2}, {1, 4}, {3}]
             + Phi[{2, 4}, {1, 3}] + Phi[{2, 4}, {3}, {1}]
            sage: Phi[[3, 5], [1, 4], [2]].coproduct()
            Phi[] # Phi[{3, 5}, {1, 4}, {2}]
             + Phi[{1}] # Phi[{4}, {1, 3}, {2}]
             + Phi[{1, 2}] # Phi[{1, 3}, {2}]
             + Phi[{2, 3}, {1}] # Phi[{2}, {1}]
             + Phi[{2, 4}, {1, 3}] # Phi[{1}]
             + Phi[{3, 5}, {1, 4}, {2}] # Phi[]

        REFERENCES:

        - Section 2.7.2 of [NovThi06]_
        """
        _prefix = "Phi"
        _basis_name = "Phi"

        def __init__(self, alg):
            """
            Initialize ``self``.

            EXAMPLES::

                sage: Phi = algebras.WQSym(QQ).Phi()
                sage: TestSuite(Phi).run()  # long time
            """
            WQSymBasis_abstract.__init__(self, alg)

            M = self.realization_of().M()
            phi = self.module_morphism(self._Phi_to_M, codomain=M, unitriangular="lower")
            phi.register_as_coercion()
            phi_inv = M.module_morphism(self._M_to_Phi, codomain=self, unitriangular="lower")
            phi_inv.register_as_coercion()

        def some_elements(self):
            """
            Return some elements of the word quasi-symmetric functions
            in the Phi basis.

            EXAMPLES::

                sage: Phi = algebras.WQSym(QQ).Phi()
                sage: Phi.some_elements()
                [Phi[], Phi[{1}], Phi[{1, 2}], Phi[] + 1/2*Phi[{1}]]
            """
            u = self.one()
            o = self([[1]])
            s = self.base_ring().an_element()
            return [u, o, self([[1,2]]), u + s*o]

        def _Phi_to_M(self, P):
            """
            Return the image of the basis element of ``self`` indexed
            by ``P`` in the Monomial basis.

            EXAMPLES::

                sage: Phi = algebras.WQSym(QQ).Phi()
                sage: OSP = Phi.basis().keys()
                sage: Phi._Phi_to_M(OSP([[2,3],[1,4]]))
                M[{2}, {3}, {1}, {4}] + M[{2}, {3}, {1, 4}]
                 + M[{2, 3}, {1}, {4}] + M[{2, 3}, {1, 4}]
                sage: Phi._Phi_to_M(OSP([[1,2],[3,4]]))
                M[{1}, {2}, {3}, {4}] + M[{1}, {2}, {3, 4}]
                 + M[{1, 2}, {3}, {4}] + M[{1, 2}, {3, 4}]
            """
            M = self.realization_of().M()
            if not P:
                return M.one()

            OSP = self.basis().keys()
            R = M.base_ring()
            one = R.one()
            return M._from_dict({OSP(G): one for G in P.strongly_finer()},
                                coerce=False)

        def _M_to_Phi(self, P):
            """
            Return the image of the basis element of the monomial
            basis indexed by ``P`` in the Phi basis ``self``.

            EXAMPLES::

                sage: Phi = algebras.WQSym(QQ).Phi()
                sage: M = algebras.WQSym(QQ).M()
                sage: OSP = Phi.basis().keys()
                sage: Phi._M_to_Phi(OSP([[2,3],[1,4]]))
                Phi[{2}, {3}, {1}, {4}] - Phi[{2}, {3}, {1, 4}]
                 - Phi[{2, 3}, {1}, {4}] + Phi[{2, 3}, {1, 4}]
                sage: Phi._M_to_Phi(OSP([[1,2],[3,4]]))
                Phi[{1}, {2}, {3}, {4}] - Phi[{1}, {2}, {3, 4}]
                 - Phi[{1, 2}, {3}, {4}] + Phi[{1, 2}, {3, 4}]

            TESTS::

                sage: Phi = algebras.WQSym(QQ).Phi()
                sage: M = algebras.WQSym(QQ).M()
                sage: OSP4 = OrderedSetPartitions(4)
                sage: all(M(Phi(M[P])) == M[P] for P in OSP4) # long time
                True
                sage: all(Phi(M(Phi[P])) == Phi[P] for P in OSP4) # long time
                True
            """
            Phi = self
            if not P:
                return Phi.one()

            OSP = self.basis().keys()
            R = self.base_ring()
            one = R.one()
            lenP = len(P)

            def sign(R):
                # the coefficient with which another
                # ordered set partition will appear
                if len(R) % 2 == lenP % 2:
                    return one
                return -one
            return Phi._from_dict({OSP(G): sign(G) for G in P.strongly_finer()},
                                  coerce=False)

        def product_on_basis(self, x, y):
            r"""
            Return the (associative) `*` product of the basis elements
            of the Phi basis ``self`` indexed by the ordered set partitions
            `x` and `y`.

            This is obtained by the following algorithm (going back to
            [NovThi06]_):

            Let `x` be an ordered set partition of `[m]`, and `y` an
            ordered set partition of `[n]`.
            Transform `x` into a list `u` of all the `m` elements of `[m]`
            by writing out each block of `x` (in increasing order) and
            putting bars between each two consecutive blocks; this is
            called a barred permutation.
            Do the same for `y`, but also shift each entry of the
            resulting barred permutation by `m`. Let `v` be the barred
            permutation of `[m+n] \setminus [m]` thus obtained.
            Now, shuffle the two barred permutations `u` and `v`
            (ignoring the bars) in all the `\binom{n+m}{n}` possible ways.
            For each shuffle obtained, place bars between some entries
            of the shuffle, according to the following rule:

            * If two consecutive entries of the shuffle both come from
              `u`, then place a bar between them if the corresponding
              entries of `u` had a bar between them.

            * If the first of two consecutive entries of the shuffle
              comes from `v` and the second from `u`, then place a bar
              between them.

            This results in a barred permutation of `[m+n]`.
            Transform it into an ordered set partition of `[m+n]`,
            by treating the bars as dividers separating consecutive
            blocks.

            The product `\Phi_x \Phi_y` is the sum of `\Phi_p` with
            `p` ranging over all ordered set partitions obtained this
            way.

            EXAMPLES::

                sage: A = algebras.WQSym(QQ).Phi()
                sage: x = OrderedSetPartition([[1],[2,3]])
                sage: y = OrderedSetPartition([[1,2]])
                sage: z = OrderedSetPartition([[1,2],[3]])
                sage: A.product_on_basis(x, y)
                Phi[{1}, {2, 3, 4, 5}] + Phi[{1}, {2, 4}, {3, 5}]
                 + Phi[{1}, {2, 4, 5}, {3}] + Phi[{1, 4}, {2, 3, 5}]
                 + Phi[{1, 4}, {2, 5}, {3}] + Phi[{1, 4, 5}, {2, 3}]
                 + Phi[{4}, {1}, {2, 3, 5}] + Phi[{4}, {1}, {2, 5}, {3}]
                 + Phi[{4}, {1, 5}, {2, 3}] + Phi[{4, 5}, {1}, {2, 3}]
                sage: A.product_on_basis(x, z)
                Phi[{1}, {2, 3, 4, 5}, {6}] + Phi[{1}, {2, 4}, {3, 5}, {6}]
                 + Phi[{1}, {2, 4, 5}, {3, 6}] + Phi[{1}, {2, 4, 5}, {6}, {3}]
                 + Phi[{1, 4}, {2, 3, 5}, {6}] + Phi[{1, 4}, {2, 5}, {3, 6}]
                 + Phi[{1, 4}, {2, 5}, {6}, {3}] + Phi[{1, 4, 5}, {2, 3, 6}]
                 + Phi[{1, 4, 5}, {2, 6}, {3}] + Phi[{1, 4, 5}, {6}, {2, 3}]
                 + Phi[{4}, {1}, {2, 3, 5}, {6}]
                 + Phi[{4}, {1}, {2, 5}, {3, 6}]
                 + Phi[{4}, {1}, {2, 5}, {6}, {3}]
                 + Phi[{4}, {1, 5}, {2, 3, 6}] + Phi[{4}, {1, 5}, {2, 6}, {3}]
                 + Phi[{4}, {1, 5}, {6}, {2, 3}] + Phi[{4, 5}, {1}, {2, 3, 6}]
                 + Phi[{4, 5}, {1}, {2, 6}, {3}] + Phi[{4, 5}, {1, 6}, {2, 3}]
                 + Phi[{4, 5}, {6}, {1}, {2, 3}]
                sage: A.product_on_basis(y, y)
                Phi[{1, 2, 3, 4}] + Phi[{1, 3}, {2, 4}] + Phi[{1, 3, 4}, {2}]
                 + Phi[{3}, {1, 2, 4}] + Phi[{3}, {1, 4}, {2}]
                 + Phi[{3, 4}, {1, 2}]

            TESTS::

                sage: one = OrderedSetPartition([])
                sage: all(A.product_on_basis(one, z) == A(z) == A.basis()[z] for z in OrderedSetPartitions(3))
                True
                sage: all(A.product_on_basis(z, one) == A(z) == A.basis()[z] for z in OrderedSetPartitions(3))
                True
                sage: M = algebras.WQSym(QQ).M()
                sage: x = A[[2, 4], [1, 3]]
                sage: y = A[[1, 3], [2]]
                sage: A(M(x) * M(y)) == x * y  # long time
                True
                sage: A(M(x) ** 2) == x**2 # long time
                True
                sage: A(M(y) ** 2) == y**2
                True
            """
            K = self.basis().keys()
            if not x:
                return self.monomial(y)
            if not y:
                return self.monomial(x)
            xlist = [(j, (k == 0))
                     for part in x
                     for (k, j) in enumerate(sorted(part))]
            # xlist is a list of the form
            # [(e_1, s_1), (e_2, s_2), ..., (e_n, s_n)],
            # where e_1, e_2, ..., e_n are the entries of the parts of
            # x in the order in which they appear in x (reading each
            # part from bottom to top), and where s_i = True if e_i is
            # the smallest element of its part and False otherwise.
            m = max(max(part) for part in x)  # The degree of x
            ylist = [(m + j, (k == 0))
                     for part in y
                     for (k, j) in enumerate(sorted(part))]
            # ylist is like xlist, but for y instead of x, and with
            # a shift by m.

            def digest(s):
                # Turn a shuffle of xlist with ylist into the appropriate
                # ordered set partition.
                s0 = [p[0] for p in s]
                s1 = [p[1] for p in s]
                N = len(s)
                bars = [False] * N
                for i in range(N-1):
                    s0i = s0[i]
                    s0i1 = s0[i+1]
                    if s0i <= m and s0i1 <= m:
                        bars[i+1] = s1[i+1]
                    elif s0i > m and s0i1 > m:
                        bars[i+1] = s1[i+1]
                    elif s0i > m and s0i1 <= m:
                        bars[i+1] = True
                blocks = []
                block = []
                for i in range(N):
                    if bars[i]:
                        blocks.append(block)
                        block = [s0[i]]
                    else:
                        block.append(s0[i])
                blocks.append(block)
                return K(blocks)
            return self.sum_of_monomials(digest(s) for s in ShuffleProduct(xlist, ylist))

        def coproduct_on_basis(self, x):
            r"""
            Return the coproduct of ``self`` on the basis element
            indexed by the ordered set partition ``x``.

            The coproduct of the basis element `\Phi_x` indexed by
            an ordered set partition `x` of `[n]` can be computed by the
            following formula ([NovThi06]_):

            .. MATH::

                \Delta \Phi_x
                = \sum \Phi_y \otimes \Phi_z ,

            where the sum ranges over all pairs `(y, z)` of ordered set
            partitions `y` and `z` such that:

            * `y` and `z` are ordered set partitions of two complementary
              subsets of `[n]`;

            * `x` is obtained either by concatenating `y` and `z`, or by
              first concatenating `y` and `z` and then merging the two
              "middle blocks" (i.e., the last block of `y` and the first
              block of `z`); in the latter case, the maximum of the last
              block of `y` has to be smaller than the minimum of the first
              block of `z` (so that when merging these blocks, their
              entries don't need to be sorted).

            EXAMPLES::

                sage: Phi = algebras.WQSym(QQ).Phi()

                sage: Phi.coproduct(Phi.one())  # indirect doctest
                Phi[] # Phi[]
                sage: Phi.coproduct( Phi([[1]]) )  # indirect doctest
                Phi[] # Phi[{1}] + Phi[{1}] # Phi[]
                sage: Phi.coproduct( Phi([[1,2]]) )
                Phi[] # Phi[{1, 2}] + Phi[{1}] # Phi[{1}] + Phi[{1, 2}] # Phi[]
                sage: Phi.coproduct( Phi([[1], [2]]) )
                Phi[] # Phi[{1}, {2}] + Phi[{1}] # Phi[{1}] + Phi[{1}, {2}] # Phi[]
                sage: Phi[[1,2],[3],[4]].coproduct()
                Phi[] # Phi[{1, 2}, {3}, {4}] + Phi[{1}] # Phi[{1}, {2}, {3}]
                 + Phi[{1, 2}] # Phi[{1}, {2}] + Phi[{1, 2}, {3}] # Phi[{1}]
                 + Phi[{1, 2}, {3}, {4}] # Phi[]

            TESTS::

                sage: M = algebras.WQSym(QQ).M()
                sage: x = Phi[[2, 4], [6], [1, 3], [5, 7]]
                sage: MM = M.tensor(M); AA = Phi.tensor(Phi)
                sage: AA(M(x).coproduct()) == x.coproduct()
                True
            """
            if not len(x):
                return self.one().tensor(self.one())
            K = self.indices()

            def standardize(P):  # standardize an ordered set partition
                base = sorted(sum((list(part) for part in P), []))
                # base is the ground set of P, as a sorted list.
                d = {val: i+1 for i,val in enumerate(base)}
                # d is the unique order isomorphism from base to
                # {1, 2, ..., |base|} (encoded as dict).
                return K([[d[x] for x in part] for part in P])
            deconcatenates = [(x[:i], x[i:]) for i in range(len(x) + 1)]
            for i in range(len(x)):
                xi = sorted(x[i])
                for j in range(1, len(xi)):
                    left = K(list(x[:i]) + [xi[:j]])
                    right = K([xi[j:]] + list(x[i+1:]))
                    deconcatenates.append((left, right))
            T = self.tensor_square()
            return T.sum_of_monomials((standardize(left), standardize(right))
                                      for (left, right) in deconcatenates)

        class Element(WQSymBasis_abstract.Element):
            def algebraic_complement(self):
                r"""
                Return the image of the element ``self`` of `WQSym`
                under the algebraic complement involution.

                See
                :meth:`WQSymBases.ElementMethods.algebraic_complement`
                for a definition of the involution and for examples.

                .. SEEALSO::

                    :meth:`coalgebraic_complement`, :meth:`star_involution`

                EXAMPLES::

                    sage: WQSym = algebras.WQSym(ZZ)
                    sage: Phi = WQSym.Phi()
                    sage: Phi[[1],[2,4],[3]].algebraic_complement()
                    -Phi[{3}, {2}, {4}, {1}] + Phi[{3}, {2, 4}, {1}] + Phi[{3}, {4}, {2}, {1}]
                    sage: Phi[[1],[2,3],[4]].algebraic_complement()
                    -Phi[{4}, {2}, {3}, {1}] + Phi[{4}, {2, 3}, {1}] + Phi[{4}, {3}, {2}, {1}]

                TESTS::

                    sage: M = WQSym.M()
                    sage: all(M(Phi[A]).algebraic_complement()
                    ....:     == M(Phi[A].algebraic_complement())
                    ....:     for A in OrderedSetPartitions(4))
                    True
                """
                # See the WQSymBases.ElementMethods.algebraic_complement doc
                # for the formula we're using here.
                BR = self.base_ring()
                one = BR.one()
                mine = -one
                Phi = self.parent()
                OSPs = Phi.basis().keys()
                from sage.data_structures.blas_dict import linear_combination

                def img(A):
                    # The image of the basis element Phi[A], written as a
                    # dictionary (of its coordinates in the Phi-basis).
                    Rs = [Rr.reversed() for Rr in A.strongly_finer()]
                    return {OSPs(P): (one if (len(R) % 2 == len(P) % 2)
                                      else mine)
                            for R in Rs for P in R.strongly_finer()}
                return Phi._from_dict(linear_combination((img(A), c) for (A, c) in self))

            def coalgebraic_complement(self):
                r"""
                Return the image of the element ``self`` of `WQSym`
                under the coalgebraic complement involution.

                See
                :meth:`WQSymBases.ElementMethods.coalgebraic_complement`
                for a definition of the involution and for examples.

                .. SEEALSO::

                    :meth:`algebraic_complement`, :meth:`star_involution`

                EXAMPLES::

                    sage: WQSym = algebras.WQSym(ZZ)
                    sage: Phi = WQSym.Phi()
                    sage: Phi[[1],[2],[3,4]].coalgebraic_complement()
                    -Phi[{4}, {3}, {1}, {2}] + Phi[{4}, {3}, {1, 2}] + Phi[{4}, {3}, {2}, {1}]
                    sage: Phi[[2],[1,4],[3]].coalgebraic_complement()
                    -Phi[{3}, {1}, {4}, {2}] + Phi[{3}, {1, 4}, {2}] + Phi[{3}, {4}, {1}, {2}]

                TESTS::

                    sage: M = WQSym.M()
                    sage: all(M(Phi[A]).coalgebraic_complement()
                    ....:     == M(Phi[A].coalgebraic_complement())
                    ....:     for A in OrderedSetPartitions(4))
                    True
                """
                # See the WQSymBases.ElementMethods.coalgebraic_complement doc
                # for the formula we're using here.
                BR = self.base_ring()
                one = BR.one()
                mine = -one
                Phi = self.parent()
                OSPs = Phi.basis().keys()
                from sage.data_structures.blas_dict import linear_combination

                def img(A):
                    # The image of the basis element Phi[A], written as a
                    # dictionary (of its coordinates in the Phi-basis).
                    Rs = [Rr.complement() for Rr in A.strongly_finer()]
                    return {OSPs(P): (one if (len(R) % 2 == len(P) % 2)
                                      else mine)
                            for R in Rs for P in R.strongly_finer()}
                return Phi._from_dict(linear_combination((img(A), c) for (A, c) in self))

            def star_involution(self):
                r"""
                Return the image of the element ``self`` of `WQSym`
                under the star involution.

                See
                :meth:`WQSymBases.ElementMethods.star_involution`
                for a definition of the involution and for examples.

                .. SEEALSO::

                    :meth:`algebraic_complement`, :meth:`coalgebraic_complement`

                EXAMPLES::

                    sage: WQSym = algebras.WQSym(ZZ)
                    sage: Phi = WQSym.Phi()
                    sage: Phi[[1,2],[5,6],[3,4]].star_involution()
                    Phi[{3, 4}, {1, 2}, {5, 6}]
                    sage: Phi[[3], [1, 2], [4]].star_involution()
                    Phi[{1}, {3, 4}, {2}]

                TESTS::

                    sage: M = WQSym.M()
                    sage: all(M(Phi[A]).star_involution() == M(Phi[A].star_involution())
                    ....:     for A in OrderedSetPartitions(4))
                    True
                """
                # See the WQSymBases.ElementMethods.star_involution doc
                # for the formula we're using here.
                Phi = self.parent()
                OSPs = Phi.basis().keys()
                return Phi._from_dict({OSPs(A.complement().reversed()): c for (A, c) in self},
                                      remove_zeros=False)

    Phi = StronglyFiner


WQSymBasis_abstract.options = WordQuasiSymmetricFunctions.options


class WQSymBases(Category_realization_of_parent):
    r"""
    The category of bases of `WQSym`.
    """
    def __init__(self, base, graded):
        r"""
        Initialize ``self``.

        INPUT:

        - ``base`` -- an instance of `WQSym`
        - ``graded`` -- boolean; if the basis is graded or filtered

        TESTS::

            sage: from sage.combinat.chas.wqsym import WQSymBases
            sage: WQSym = algebras.WQSym(ZZ)
            sage: bases = WQSymBases(WQSym, True)
            sage: WQSym.M() in bases
            True
        """
        self._graded = graded
        Category_realization_of_parent.__init__(self, base)

    def _repr_(self):
        r"""
        Return the representation of ``self``.

        EXAMPLES::

            sage: from sage.combinat.chas.wqsym import WQSymBases
            sage: WQSym = algebras.WQSym(ZZ)
            sage: WQSymBases(WQSym, True)
            Category of graded bases of Word Quasi-symmetric functions over Integer Ring
            sage: WQSymBases(WQSym, False)
            Category of filtered bases of Word Quasi-symmetric functions over Integer Ring
        """
        if self._graded:
            type_str = "graded"
        else:
            type_str = "filtered"
        return "Category of {} bases of {}".format(type_str, self.base())

    def super_categories(self):
        r"""
        The super categories of ``self``.

        EXAMPLES::

            sage: from sage.combinat.chas.wqsym import WQSymBases
            sage: WQSym = algebras.WQSym(ZZ)
            sage: bases = WQSymBases(WQSym, True)
            sage: bases.super_categories()
            [Category of realizations of Word Quasi-symmetric functions over Integer Ring,
             Join of Category of realizations of hopf algebras over Integer Ring
                 and Category of graded algebras over Integer Ring
                 and Category of graded coalgebras over Integer Ring,
             Category of graded connected hopf algebras with basis over Integer Ring]

            sage: bases = WQSymBases(WQSym, False)
            sage: bases.super_categories()
            [Category of realizations of Word Quasi-symmetric functions over Integer Ring,
             Join of Category of realizations of hopf algebras over Integer Ring
                 and Category of graded algebras over Integer Ring
                 and Category of graded coalgebras over Integer Ring,
             Join of Category of filtered connected hopf algebras with basis over Integer Ring
                 and Category of graded algebras over Integer Ring
                 and Category of graded coalgebras over Integer Ring]
        """
        R = self.base().base_ring()
        cat = HopfAlgebras(R).Graded().WithBasis()
        if self._graded:
            cat = cat.Graded()
        else:
            cat = cat.Filtered()
        return [self.base().Realizations(),
                HopfAlgebras(R).Graded().Realizations(),
                cat.Connected()]

    class ParentMethods:
        def _repr_(self):
            """
            Text representation of this basis of `WQSym`.

            EXAMPLES::

                sage: WQSym = algebras.WQSym(ZZ)
                sage: WQSym.M()
                Word Quasi-symmetric functions over Integer Ring in the Monomial basis
            """
            return "{} in the {} basis".format(self.realization_of(), self._basis_name)

        def __getitem__(self, p):
            """
            Return the basis element indexed by ``p``.

            INPUT:

            - ``p`` -- an ordered set partition

            EXAMPLES::

                sage: M = algebras.WQSym(QQ).M()
                sage: M[1, 2, 1]  # pass a word
                M[{1, 3}, {2}]
                sage: _ == M[[1, 2, 1]] == M[Word([1,2,1])]
                True
                sage: M[[1, 2, 3]]
                M[{1}, {2}, {3}]

                sage: M[[[1, 2, 3]]]  # pass an ordered set partition
                M[{1, 2, 3}]
                sage: _ == M[[1,2,3],] == M[OrderedSetPartition([[1,2,3]])]
                True
                sage: M[[1,3],[2]]
                M[{1, 3}, {2}]

            TESTS::

                sage: M[[]]
                M[]
                sage: M[1, 2, 1] == M[Word([2,3,2])] == M[Word('aca')]
                True
                sage: M[[[1,2]]] == M[1,1] == M[1/1,2/2] == M[2/1,2/1] == M['aa']
                True
                sage: M[1] == M[1,] == M[Word([1])] == M[OrderedSetPartition([[1]])] == M[[1],]
                True
            """
            if p in ZZ:
                p = [ZZ(p)]
            if all(s in ZZ for s in p):
                return self.monomial(self._indices.from_finite_word([ZZ(s) for s in p]))

            if all(isinstance(s, str) for s in p):
                return self.monomial(self._indices.from_finite_word(p))
            try:
                return self.monomial(self._indices(p))
            except TypeError:
                raise ValueError("cannot convert %s into an element of %s" % (p, self._indices))

        def is_field(self, proof=True):
            """
            Return whether ``self`` is a field.

            EXAMPLES::

                sage: M = algebras.WQSym(QQ).M()
                sage: M.is_field()
                False
            """
            return False

        def is_commutative(self):
            """
            Return whether ``self`` is commutative.

            EXAMPLES::

                sage: M = algebras.WQSym(ZZ).M()
                sage: M.is_commutative()
                False
            """
            return self.base_ring().is_zero()

        def one_basis(self):
            """
            Return the index of the unit.

            EXAMPLES::

                sage: A = algebras.WQSym(QQ).M()
                sage: A.one_basis()
                []
            """
            OSP = self.basis().keys()
            return OSP([])

        def degree_on_basis(self, t):
            """
            Return the degree of an ordered set partition in
            the algebra of word quasi-symmetric functions.

            This is the sum of the sizes of the blocks of the
            ordered set partition.

            EXAMPLES::

                sage: A = algebras.WQSym(QQ).M()
                sage: u = OrderedSetPartition([[2,1],])
                sage: A.degree_on_basis(u)
                2
                sage: u = OrderedSetPartition([[2], [1]])
                sage: A.degree_on_basis(u)
                2
            """
            return sum(len(part) for part in t)

        @cached_method
        def labelled_tree_to_Basis(self, t):
            """
                sage: R = algebras.WQSym(QQ).R()
                sage: R.options.objects = 'words'
                sage: pw = PackedWord([1])
                sage: t = pw.packed_word_to_labelled_tree(); ascii_art(t)
                (0, [1])
                sage: R.labelled_tree_to_Basis(t)
                R[1]
                sage: pw = PackedWord([1,2])
                sage: t = pw.packed_word_to_labelled_tree(); ascii_art(t)
                (1, [1])
                |
                (0, [1])
                sage: R.labelled_tree_to_Basis(t)
                R[1, 2] - R[2, 1]
                sage: pw = PackedWord([1,3,4,2])
                sage: t = pw.packed_word_to_labelled_tree(); ascii_art(t)
                (0, [3])
                |
                (0, [2])
                |
                (1, [1])
                |
                (0, [1])
                sage: R.labelled_tree_to_Basis(t)
                R[1, 3, 4, 2] - R[2, 3, 4, 1]
                sage: pw = PackedWord([1,1])
                sage: t = pw.packed_word_to_labelled_tree(); ascii_art(t)
                (0, [1, 2])
                sage: R.labelled_tree_to_Basis(t)
                R[1, 1]
                sage: pw = PackedWord([1,3,1,2])
                sage: t = pw.packed_word_to_labelled_tree(); ascii_art(t)
                (0, [2])
                |
                (1, [1])
                |
                (0, [1, 2])
                sage: R.labelled_tree_to_Basis(t)
                R[1, 3, 1, 2] - R[2, 3, 2, 1]
                sage: pw = PackedWord([2,1,1,2])
                sage: t = pw.packed_word_to_labelled_tree(); ascii_art(t)
                (0, [1, 4])
                |
                (0, [1, 2])
                sage: R.labelled_tree_to_Basis(t)
                R[2, 1, 1, 2]
                sage: pw = PackedWord([2,1,2,1])
                sage: t = pw.packed_word_to_labelled_tree(); ascii_art(t)
                (0, [1, 3])
                |
                (0, [1, 2])
                sage: R.labelled_tree_to_Basis(t)
                R[2, 1, 2, 1]

            
                sage: Q = algebras.WQSym(QQ).Q()
                sage: Q.options.objects = 'words'
                sage: pw = PackedWord([1])
                sage: t = pw.packed_word_to_labelled_tree_left(); ascii_art(t)
                (0, (1, False))
                sage: Q.labelled_tree_to_Basis(t)
                Q[1]
                sage: pw = PackedWord([1,2])
                sage: t = pw.packed_word_to_labelled_tree_left(); ascii_art(t)
                (1, (1, False))
                |
                (0, (1, False))
                sage: Q.labelled_tree_to_Basis(t)
                Q[1, 2] - Q[2, 1]
                sage: pw = PackedWord([1,3,4,2])
                sage: t = pw.packed_word_to_labelled_tree_left(); ascii_art(t)
                (0, (2, False))
                |
                (1, (1, False))
                |
                (1, (1, False))
                |
                (0, (1, False))
                sage: Q.labelled_tree_to_Basis(t)
                Q[1, 3, 4, 2] - Q[3, 1, 4, 2] - Q[4, 1, 3, 2] + Q[4, 3, 1, 2]
                sage: pw = PackedWord([1,1])
                sage: t = pw.packed_word_to_labelled_tree_left(); ascii_art(t)
                (0, (1, True))
                |
                (0, (1, False))
                sage: Q.labelled_tree_to_Basis(t)
                Q[1, 1]
                sage: pw = PackedWord([1,3,1,2])
                sage: t = pw.packed_word_to_labelled_tree_left(); ascii_art(t)
                (0, (2, False))
                |
                (0, (1, True))
                |
                (1, (1, False))
                |
                (0, (1, False))
                sage: Q.labelled_tree_to_Basis(t)
                Q[1, 3, 1, 2] - Q[3, 1, 1, 2]
                sage: pw = PackedWord([2,1,1,2])
                sage: t = pw.packed_word_to_labelled_tree_left(); ascii_art(t)
                _______(1, (1, True))
                /               /              
                (0, (1, True))  (0, (1, False))
                |              
                (0, (1, False))
                sage: Q.labelled_tree_to_Basis(t)
                Q[1, 1, 2, 2] - Q[2, 2, 1, 1]
                sage: pw = PackedWord([2,1,2,1])
                sage: t = pw.packed_word_to_labelled_tree_left(); ascii_art(t)
                (0, (1, True))
                |
                _______(1, (1, True))
                /               /              
                (0, (1, False)) (0, (1, False))
                sage: Q.labelled_tree_to_Basis(t)
                Q[1, 2, 2, 1] - Q[2, 2, 1, 1]
            """
            #import pdb; pdb.set_trace()
            if self._prefix == 'R':
                cut, pos = t.label()
                f = t[cut:]

                if len(t) <= cut or len(t) == 0:
                    root = self.monomial(OrderedSetPartition([pos]))
                else:
                    root = self.labelled_forest_to_Basis(f).Upgrade([x-1 for x in pos])


            elif self._prefix == 'Q':
                cut, (val, b) = t.label()
                f = t[cut:]

                if len(t) <= cut or len(t) == 0:
                    root = self.monomial(OrderedSetPartition([1]))
                elif len(f) == 1:
                    root = self.labelled_tree_to_Basis(f[0]).Upgrade((val,b))

            return self.brackets([self.labelled_tree_to_Basis(tt) for tt in
                                  t[:cut]]+[root])

                    
            # return self.brackets([self.labelled_tree_to_Basis(tt) for tt in t[1:]] +
            #                      [self.labelled_tree_to_Basis(
            #                          LabelledOrderedTree([t[0]], t.label()))])


            # if type(t.label()) is Integer:
                
            #     return self.monomial(OrderedSetPartition([range(1,t.label()+1)]))

            
            # lbl = t.label()
            # star = (lbl[-1] == '*')
            # if star:
            #     lbl = int(lbl[:-1])
            # else:
            #     lbl = int(lbl)
                        
            # if lbl == 0 and not star:
            #     return self.brackets([self.labelled_tree_to_Basis(tt) for tt in t] + [self[1]])
            
            # if len(t) == 1 and not star:
            #     # if star:
            #     #     M = len(filter(lambda label: label[-1] != '*', t.labels()))
            #     #     return sum(self.labelled_tree_to_Basis(t[0]).LPhi(lbl, k+1)
            #     #                for k in range(0, M))
            #         # return self.labelled_tree_to_Basis(t[0]).LPhi(i[0])
            #     return self.labelled_tree_to_Basis(t[0]).LPhi(lbl)

            # def is_particular(t):
            #     if len(t) == 0:
            #         return True
            #     lbl = t.label()
            #     star = (lbl[-1] == '*')
            #     if star:
            #         lbl = int(lbl[:-1])
            #     else:
            #         lbl = int(lbl)
                    
            #     if len(t) == 1 and not star and lbl != 0:
            #         return True
            #     if star:
            #         return is_particular(t[-1])
            #     return False

            # def star_cut(t):
            #     lbl = t.label()
            #     star = (lbl[-1] == '*')
            #     if star:
            #         lbl = int(lbl[:-1])
            #     else:
            #         lbl = int(lbl)
                
            #     if star:
            #         ttk,f = star_cut(t[-1])
            #         return (LabelledOrderedTree([tt for tt in t[:-1]] + [ttk], t.label()),f)

            #     if lbl == 0:
            #         return (LabelledOrderedTree([], t.label()), [tt for tt in t])
            #     return (LabelledOrderedTree([t[0]], t.label()), [tt for tt in t[1:]])
                
            # if star:
            #     # import pdb; pdb.set_trace()
            #     tt,f = star_cut(t) # découpe de l'arbre en prim_tot + foret (A = AP * (F+1))
            #     #f = f[::-1] # inversion de la foret ??
            #     ff = [ttt for ttt in tt] # les sous-arbres après découpe, inversé ??
            #     M = len(filter(lambda label: label[-1] != '*', tt.labels())) # t.node_number()
            #     m = M - len(filter(lambda label: label[-1] != '*', tt[-1].labels()))
            #     #t[0].node_number()+1
            #     root =  sum(self.labelled_forest_to_Basis(ff).LPhi(lbl,k+1)
            #                 for k in range(m, M)) # tt dans la base
            #     return self.brackets([self.labelled_tree_to_Basis(tt) for tt in f]+[root])

            # return self.brackets([self.labelled_tree_to_Basis(tt) for tt in t[1:]] +
            #                      [self.labelled_tree_to_Basis(
            #                          LabelledOrderedTree([t[0]], t.label()))])
        
        def labelled_forest_to_Basis(self, f):
            """
                sage: R = algebras.WQSym(QQ).R()
                sage: R.options.objects = 'words'

sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
#sage: O.options.objects = 'words'
sage: matr_chgmt_base_osp = lambda X,Y, n: matrix([[Y(X(mu)).coefficient(sigma) for mu in OrderedSetPartitions(n)] for sigma in OrderedSetPartitions(n)])
sage: PW = PackedWord
sage: matr_chgmt_base_perm = lambda X,Y, n: matrix([[Y(X[PW(mu).to_ordered_set_partition()]).coefficient(PW(sigma).to_ordered_set_partition())
....:                                          for mu in Permutations(n)]
....:                                          for sigma in Permutations(n)])
sage: matr_chgmt_base_osp(P,R,3)
sage: matr_chgmt_base_perm(P,R,3)
sage: _.rank()
                sage: for p in PackedWords(3):
                ....:     print p
                ....:     f = p.packed_word_to_labelled_forest(); ascii_art(f)
                ....:     print R.labelled_forest_to_Basis(f)
                ....:     print 
sage: ascii_art(P[1,2]*P[1,2])
[ (1, [1]) ]                                                  
[ |        ]                                                  
[ (1, [1]) ]   [   ___(2, [1])      ]   [   ___(2, [1])      ]
[ |        ]   [  /        /        ]   [  /        /        ]
[ (1, [1]) ]   [ (0, [1]) (1, [1])  ]   [ (1, [1]) (0, [1])  ]     [ (1, [1]), (1, [1]) ]
[ |        ]   [          |         ]   [ |                  ]     [ |         |        ]
[ (0, [1]) ] + [          (0, [1])  ] + [ (0, [1])           ] + 2*[ (0, [1])  (0, [1]) ]
            """
            if len(f) == 0:
                return self.zero()
            if len(f) == 1:
                return self.labelled_tree_to_Basis(f[0])
            res = self.labelled_forest_to_Basis(f[:-1])
            return self.left_product(self.labelled_tree_to_Basis(f[-1]), res)

        def product_by_coercion(self, x, y):
            if self._prefix in ['O']:
                B = self.realization_of().Q()
            elif self._prefix in ['P']:
                B = self.realization_of().R()
            else:
                B = self.realization_of().a_realization()
            return self(B(x) * B(y))
            
        
        # HuxoD pour le bidendriforme

        @lazy_attribute
        def right_product(self):
            r"""
            Return the `\succ` product.

            On the F-basis of ``FQSym``, this product is determined by
            `F_x \succ F_y = \sum F_z`, where the sum ranges over all `z`
            in the shifted shuffle of `x` and `y` with the additional
            condition that the first letter of the result comes from `y`.

            The usual symbol for this operation is `\succ`.

            .. SEEALSO::

                :meth:`~sage.categories.magmas.Magmas.ParentMethods.product`,
                :meth:`left`

            EXAMPLES::

                sage: R = algebras.WQSym(QQ).R()
                sage: o = R[1]
                sage: x = R[1,1,2]
                sage: y = R[2,1,1]
                sage: R.right_product(o, o)
                R[1, 2]
                sage: R.right_product(o, x)
                R[1, 2, 2, 3] + R[2, 1, 2, 3] + R[2, 2, 1, 3]
                sage: R.right_product(y, x)
                R[2, 1, 1, 3, 3, 4] + R[2, 1, 3, 1, 3, 4] + R[2, 1, 3, 3, 1, 4] + R[2, 3, 1, 1, 3, 4] + R[3, 2, 1, 1, 3, 4] + R[2, 3, 1, 3, 1, 4] + R[3, 2, 1, 3, 1, 4] + R[2, 3, 3, 1, 1, 4] + R[3, 2, 3, 1, 1, 4] + R[3, 3, 2, 1, 1, 4]
            """
            try:
                right = self.right_product_on_basis
            except AttributeError:
                return self.right_by_coercion
            return self._module_morphism(self._module_morphism(right, position=0,
                                                               codomain=self),
                                         position=1)

        def right_by_coercion(self, x, y):
            r"""
            Return `x \succ y`, computed using coercion to the F-basis.

            See :meth:`right` for the definition of the objects involved.

            EXAMPLES::

                sage: G = algebras.FQSym(ZZ).G()
                sage: G.right(G([1]), G([2, 3, 1])) # indirect doctest
                G[2, 3, 4, 1] + G[3, 2, 4, 1] + G[4, 2, 3, 1]
            """
            if self._prefix in ['M', 'O']:
                B = self.realization_of().Q()
            elif self._prefix in ['P']:
                B = self.realization_of().R()
            else:
                raise NotImplementedError
            return self(B.right_product(B(x), B(y)))

        @lazy_attribute
        def right_coproduct(self):
            """
            TESTS::

sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
#sage: H.options.objects = 'words'
sage: R.right_coproduct(R[1,2,2])
            """
            try:
                right = self.right_coproduct_on_basis
            except AttributeError:
                return self.right_coproduct_by_coercion
            return self._module_morphism(right, position=0, codomain=self.tensor(self))

        def right_coproduct_by_coercion(self, x):
            r"""
            TESTS::

sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
#sage: H.options.objects = 'words'
sage: HD.right_coproduct(HD[1,2,2])
            """
            if self._prefix in ['M', 'O']:
                B = self.realization_of().Q()
            elif self._prefix in ['P']:
                B = self.realization_of().R()
            else:
                raise NotImplementedError
            coproduct_B = B.right_coproduct(B(x))
            res = 0
            for (l, r) in coproduct_B.monomial_coefficients():
                res += coproduct_B[(l, r)] * tensor((self(B[l]), self(B[r])))
            return res
            
        @lazy_attribute
        def left_product(self):
            r"""
            Return the `\left` product.

            On the F-basis of ``FQSym``, this product is determined by
            `F_x \left F_y = \sum F_z`, where the sum ranges over all `z`
            in the shifted shuffle of `x` and `y` with the additional
            condition that the first letter of the result comes from `x`.

            The usual symbol for this operation is `\left`.

            .. SEEALSO::

                :meth:`~sage.categories.magmas.Magmas.ParentMethods.product`,
                :meth:`right`

            EXAMPLES::

                sage: A = algebras.FQSym(QQ).F()
                sage: x = A([2,1])
                sage: A.left(x, x)
                F[2, 1, 4, 3] + F[2, 4, 1, 3] + F[2, 4, 3, 1]
                sage: y = A([2,1,3])
                sage: A.left(x, y)
                F[2, 1, 4, 3, 5] + F[2, 4, 1, 3, 5] + F[2, 4, 3, 1, 5]
                 + F[2, 4, 3, 5, 1]
                sage: A.left(y, x)
                F[2, 1, 3, 5, 4] + F[2, 1, 5, 3, 4] + F[2, 1, 5, 4, 3]
                 + F[2, 5, 1, 3, 4] + F[2, 5, 1, 4, 3] + F[2, 5, 4, 1, 3]
            """
            try:
                left = self.left_product_on_basis
            except AttributeError:
                return self.left_by_coercion
            return self._module_morphism(self._module_morphism(left, position=0,
                                                               codomain=self),
                                         position=1)

        def left_by_coercion(self, x, y):
            r"""
            Return `x \prec y`, computed using coercion to the F-basis.

            See :meth:`left` for the definition of the objects involved.

            EXAMPLES::

                sage: G = algebras.FQSym(ZZ).G()
                sage: a = G([1])
                sage: b = G([2, 3, 1])
                sage: G.left(a, b) + G.right(a, b) == a * b # indirect doctest
                True
            """
            if self._prefix in ['M', 'O']:
                B = self.realization_of().Q()
            elif self._prefix in ['P']:
                B = self.realization_of().R()
            else:
                raise NotImplementedError
            return self(B.left_product(B(x), B(y)))

        # @lazy_attribute
        # def left_concat(self):
        #     r"""
        #     Return the `\left` product.

        #     On the F-basis of ``FQSym``, this product is determined by
        #     `F_x \left F_y = \sum F_z`, where the sum ranges over all `z`
        #     in the shifted shuffle of `x` and `y` with the additional
        #     condition that the first letter of the result comes from `x`.

        #     The usual symbol for this operation is `\left`.

        #     .. SEEALSO::

        #         :meth:`~sage.categories.magmas.Magmas.ParentMethods.product`,
        #         :meth:`right`

        #     EXAMPLES::

        #         sage: A = algebras.FQSym(QQ).F()
        #         sage: x = A([2,1])
        #         sage: A.left(x, x)
        #         F[2, 1, 4, 3] + F[2, 4, 1, 3] + F[2, 4, 3, 1]
        #         sage: y = A([2,1,3])
        #         sage: A.left(x, y)
        #         F[2, 1, 4, 3, 5] + F[2, 4, 1, 3, 5] + F[2, 4, 3, 1, 5]
        #          + F[2, 4, 3, 5, 1]
        #         sage: A.left(y, x)
        #         F[2, 1, 3, 5, 4] + F[2, 1, 5, 3, 4] + F[2, 1, 5, 4, 3]
        #          + F[2, 5, 1, 3, 4] + F[2, 5, 1, 4, 3] + F[2, 5, 4, 1, 3]
        #     """
        #     try:
        #         left = self.left_concat_on_basis
        #     except AttributeError:
        #         return self.left_concat_by_coercion
        #     return self._module_morphism(self._module_morphism(left, position=0,
        #                                                        codomain=self),
        #                                  position=1)

        # def left_concat_by_coercion(self, x, y):
        #     r"""
        #     Return `x \prec y`, computed using coercion to the F-basis.

        #     See :meth:`left` for the definition of the objects involved.

        #     EXAMPLES::

        #         sage: G = algebras.FQSym(ZZ).G()
        #         sage: a = G([1])
        #         sage: b = G([2, 3, 1])
        #         sage: G.left(a, b) + G.right(a, b) == a * b # indirect doctest
        #         True
        #     """
        #     R = self.realization_of().R()
        #     return self(R.left_concat(R(x), R(y))) #last

        @lazy_attribute
        def left_coproduct(self):
            """
            TESTS::

sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
#sage: H.options.objects = 'words'
sage: R.left_coproduct(R[1,2,2])
sage: R[1,2,2].left_coproduct()
            """
            try:
                left = self.left_coproduct_on_basis
            except AttributeError:
                return self.left_coproduct_by_coercion
            return self._module_morphism(left, position=0, codomain=self.tensor(self))   
            
        def left_coproduct_by_coercion(self, x):
            r"""
            TESTS::

sage: WQSym = algebras.WQSym(QQ)
sage: WQSym.inject_shorthands()
#sage: H.options.objects = 'words'
sage: HD.left_coproduct(HD[1,2,2])
            """
            if self._prefix in ['M', 'O']:
                B = self.realization_of().Q()
            elif self._prefix in ['P']:
                B = self.realization_of().R()
            else:
                raise NotImplementedError
            coproduct_B = B.left_coproduct(B(x))
            res = 0
            for (l, r) in coproduct_B.monomial_coefficients():
                res += coproduct_B[(l, r)] * tensor((self(B[l]), self(B[r])))
            return res

    class ElementMethods:
        def __rshift__(self, right):
            '''
            .. FIXME:: must be done
            attention.... c + b << a == (c+b)<<a
            '''
            if self.parent() == right.parent() and\
               hasattr(self.parent(), "right_product"):
                return self.parent().right_product(self, right)
            from sage.structure.element import get_coercion_model
            import operator
            return get_coercion_model().bin_op(self, right, operator.rshift)

        def __lshift__(self, right):
            '''
            .. FIXME:: must be done
            '''
            if self.parent() == right.parent() and \
               hasattr(self.parent(), "left_product"):
                return self.parent().left_product(self, right)
            from sage.structure.element import get_coercion_model
            import operator
            return get_coercion_model().bin_op(self, right, operator.lshift)
        
        # HuxoD End pour le bidendriforme
        
        def Upgrade(self, l):
            """
                sage: R = algebras.WQSym(QQ).R()
                sage: R.options.objects = 'words'
                sage: x = R[1,1,2] + R[2,1,1]
                sage: x.Upgrade([1,2])
                R[1, 3, 3, 1, 2] + R[2, 3, 3, 1, 1]
                sage: x.Upgrade([2])
                R[1, 3, 1, 2] + R[2, 3, 1, 1]
                sage: Q = algebras.WQSym(QQ).Q()
                sage: Q.options.objects = 'words'
                sage: x = Q[1,1,2] + Q[2,1,1]
                sage: x.Upgrade((2,True))
                Q[1, 1, 2, 2] + Q[2, 1, 1, 2]
                sage: x.Upgrade((2,False))
                Q[1, 1, 3, 2] + Q[3, 1, 1, 2]
            """
            B = self.parent()
            res = 0
            xm = self.monomial_coefficients()
            for k in xm:
                if B._prefix == 'R':
                    res += xm[k] * B.monomial(OrderedSetPartition(PackedWord(k.to_packed_word()).upgrade_max(l)))
                elif B._prefix == 'Q':
                    res += xm[k] * B.monomial(OrderedSetPartition(PackedWord(k.to_packed_word()).upgrade_last(l)))# [k.lphi_l(p)]
                        # up = k.upgrade_max(p)
                        # res += xm[k] * sum(up[x] * B.monomial(x) for x in up)
                    # raise NotImplementedError # 
                else:
                    raise ValueError("The basis must be `R` or `Q`.")
                    
                # res += xm[k] * sum(B[PackedWord(k.to_packed_word()).lphi(i, m)]
                #                    for m in range(1, len(k) + 1))
            return res

        def left_shifted_concat(self, other):
            """
                sage: M = algebras.WQSym(QQ).M()
                sage: M.options.objects = 'words'
                sage: x = M[1,1,2] + 2 * M[2,1,1]
                sage: y = 3 * M[1,2] - 5 * M[1,3,2,2]
                sage: x.left_shifted_concat(y)
                3*M[3, 4, 1, 1, 2] + 6*M[3, 4, 2, 1, 1] - 5*M[3, 5, 4, 4, 1, 1, 2] - 10*M[3, 5, 4, 4, 2, 1, 1]
            """
            B = self.parent()
            res = 0
            xm = self.monomial_coefficients()
            ym = other.monomial_coefficients()
            for k in xm:
                for l in ym:
                    kshifted = [{i+l.size() for i in j} for j in k]
                    res += xm[k] * ym[l] * B[kshifted + list(l)]

            return res

        def right_shifted_concat(self, other):
            """
                sage: M = algebras.WQSym(QQ).M()
                sage: M.options.objects = 'words'
                sage: x = M[1,1,2] + 2 * M[2,1,1]
                sage: y = 3 * M[1,2] - 5 * M[1,3,2,2]
                sage: x.right_shifted_concat(y)
                3*M[1, 1, 2, 3, 4] - 5*M[1, 1, 2, 3, 5, 4, 4] + 6*M[2, 1, 1, 3, 4] - 10*M[2, 1, 1, 3, 5, 4, 4]
            """
            B = self.parent()
            res = 0
            xm = self.monomial_coefficients()
            ym = other.monomial_coefficients()
            for k in xm:
                for l in ym:
                    lshifted = [{i+k.size() for i in j} for j in l]
                    res += xm[k] * ym[l] * B[list(k) + lshifted]

            return res
        
        def algebraic_complement(self):
            r"""
            Return the image of the element ``self`` of `WQSym`
            under the algebraic complement involution.

            If `u = (u_1, u_2, \ldots, u_n)` is a packed word
            that contains the letters `1, 2, \ldots, k` and no
            others, then the *complement* of `u` is defined to
            be the packed word
            `\overline{u} := (k+1 - u_1, k+1 - u_2, \ldots, k+1 - u_n)`.

            The algebraic complement involution is defined as the
            linear map `WQSym \to WQSym` that sends each basis
            element `\mathbf{M}_u` of the monomial basis of `WQSym`
            to the basis element `\mathbf{M}_{\overline{u}}`.
            This is a graded algebra automorphism and a coalgebra
            anti-automorphism of `WQSym`.
            Denoting by `\overline{f}` the image of an element
            `f \in WQSym` under the algebraic complement involution,
            it can be shown that every packed word `u` satisfies

            .. MATH::

                \overline{\mathbf{M}_u} = \mathbf{M}_{\overline{u}},
                \qquad \overline{X_u} = X_{\overline{u}},

            where standard notations for classical bases of `WQSym`
            are being used (that is, `\mathbf{M}` for the monomial
            basis, and `X` for the characteristic basis).

            This can be restated in terms of ordered set partitions:
            For any ordered set partition `R = (R_1, R_2, \ldots, R_k)`,
            let `R^r` denote the ordered set partition
            `(R_k, R_{k-1}, \ldots, R_1)`; this is known as
            the *reversal* of `R`. Then,

            .. MATH::

                \overline{\mathbf{M}_A} = \mathbf{M}_{A^r}, \qquad
                \overline{X_A} = X_{A^r}

            for any ordered set partition `A`.

            The formula describing algebraic complements on the Q basis
            (:class:`WordQuasiSymmetricFunctions.StronglyCoarser`)
            is more complicated, and requires some definitions.
            We define a partial order `\leq` on the set of all ordered
            set partitions as follows: `A \leq B` if and only if
            `A` is strongly finer than `B` (see
            :meth:`~sage.combinat.set_partition_ordered.OrderedSetPartition.is_strongly_finer`
            for a definition of this).
            The *length* `\ell(R)` of an ordered set partition `R` shall
            be defined as the number of parts of `R`.
            Use the notation `Q` for the Q basis.
            For any ordered set partition `A` of `[n]`, we have

            .. MATH::

                \overline{Q_A} = \sum_P c_{A, P} Q_P,

            where the sum is over all ordered set partitions `P` of
            `[n]`, and where the coefficient `c_{A, P}` is defined
            as follows:

            * If there exists an ordered set partition `R` satisfying
              `R \leq P` and `A \leq R^r`, then this `R` is unique,
              and `c_{A, P} = \left(-1\right)^{\ell(R) - \ell(P)}`.

            * If there exists no such `R`, then `c_{A, P} = 0`.

            The formula describing algebraic complements on the `\Phi`
            basis (:class:`WordQuasiSymmetricFunctions.StronglyFiner`)
            is identical to the above formula for the Q basis, except
            that the `\leq` sign has to be replaced by `\geq` in the
            definition of the coefficients `c_{A, P}`. In fact, both
            formulas are particular cases of a general formula for
            involutions:
            Assume that `V` is an (additive) abelian group, and that
            `I` is a poset. For each `i \in I`, let `M_i` be an element
            of `V`. Also, let `\omega` be an involution of the set `I`
            (not necessarily order-preserving or order-reversing),
            and let `\omega'` be an involutive group endomorphism of
            `V` such that each `i \in I` satisfies
            `\omega'(M_i) = M_{\omega(i)}`.
            For each `i \in I`, let `F_i = \sum_{j \geq i} M_j`,
            where we assume that the sum is finite.
            Then, each `i \in I` satisfies

            .. MATH::

                \omega'(F_i)
                = \sum_j \sum_{\substack{k \leq j; \\ \omega(k) \geq i}}
                  \mu(k, j) F_j,

            where `\mu` denotes the Möbius function. This formula becomes
            particularly useful when the `k` satisfying `k \leq j`
            and `\omega(k) \geq i` is unique (if it exists).
            In our situation, `V` is `WQSym`, and `I` is the set of
            ordered set partitions equipped either with the `\leq` partial
            order defined above or with its opposite order.
            The `M_i` is the `\mathbf{M}_A`, whereas the `F_i` is either
            `Q_i` or `\Phi_i`.

            If we denote the star involution
            (:meth:`~sage.combinat.ncsf_qsym.qsym.QuasiSymmetricFunctions.Bases.ElementMethods.star_involution`)
            of the quasisymmetric functions by `f \mapsto f^{\ast}`,
            and if we let `\pi` be the canonical projection
            `WQSym \to QSym`, then each `f \in WQSym` satisfies
            `\pi(\overline{f}) = (\pi(f))^{\ast}`.

            .. SEEALSO::

                :meth:`coalgebraic_complement`, :meth:`star_involution`

            EXAMPLES:

            Recall that the index set for the bases of `WQSym` is
            given by ordered set partitions, not packed words.
            Translated into the language of ordered set partitions,
            the algebraic complement involution acts on the
            Monomial basis by reversing the ordered set partition.
            In other words, we have

            .. MATH::

                \overline{\mathbf{M}_{(P_1, P_2, \ldots, P_k)}}
                = \mathbf{M}_{(P_k, P_{k-1}, \ldots, P_1)}

            for any standard ordered set partition
            `(P_1, P_2, \ldots, P_k)`. Let us check this in practice::

                sage: WQSym = algebras.WQSym(ZZ)
                sage: M = WQSym.M()
                sage: M[[1,3],[2]].algebraic_complement()
                M[{2}, {1, 3}]
                sage: M[[1,4],[2,5],[3,6]].algebraic_complement()
                M[{3, 6}, {2, 5}, {1, 4}]
                sage: (3*M[[1]] - 4*M[[]] + 5*M[[1],[2]]).algebraic_complement()
                -4*M[] + 3*M[{1}] + 5*M[{2}, {1}]
                sage: X = WQSym.X()
                sage: X[[1,3],[2]].algebraic_complement()
                X[{2}, {1, 3}]
                sage: C = WQSym.C()
                sage: C[[1,3],[2]].algebraic_complement()
                -C[{1, 2, 3}] - C[{1, 3}, {2}] + C[{2}, {1, 3}]
                sage: Q = WQSym.Q()
                sage: Q[[1,2],[5,6],[3,4]].algebraic_complement()
                Q[{3, 4}, {1, 2, 5, 6}] + Q[{3, 4}, {5, 6}, {1, 2}] - Q[{3, 4, 5, 6}, {1, 2}]
                sage: Phi = WQSym.Phi()
                sage: Phi[[2], [1,3]].algebraic_complement()
                -Phi[{1}, {3}, {2}] + Phi[{1, 3}, {2}] + Phi[{3}, {1}, {2}]

            The algebraic complement involution intertwines the antipode
            and the inverse of the antipode::

                sage: all( M(I).antipode().algebraic_complement().antipode()  # long time
                ....:      == M(I).algebraic_complement()
                ....:      for I in OrderedSetPartitions(4) )
                True

            Testing the `\pi(\overline{f}) = (\pi(f))^{\ast}` relation::

                sage: all( M[I].algebraic_complement().to_quasisymmetric_function()
                ....:      == M[I].to_quasisymmetric_function().star_involution()
                ....:      for I in OrderedSetPartitions(4) )
                True

            .. TODO::

                Check further commutative squares.
            """
            # Convert to the Monomial basis, there apply the algebraic
            # complement componentwise, then convert back.
            parent = self.parent()
            M = parent.realization_of().M()
            dct = {I.reversed(): coeff for (I, coeff) in M(self)}
            return parent(M._from_dict(dct, remove_zeros=False))

        def coalgebraic_complement(self):
            r"""
            Return the image of the element ``self`` of `WQSym`
            under the coalgebraic complement involution.

            If `u = (u_1, u_2, \ldots, u_n)` is a packed word,
            then the *reversal* of `u` is defined to be the
            packed word `(u_n, u_{n-1}, \ldots, u_1)`.
            This reversal is denoted by `u^r`.

            The coalgebraic complement involution is defined as the
            linear map `WQSym \to WQSym` that sends each basis
            element `\mathbf{M}_u` of the monomial basis of `WQSym`
            to the basis element `\mathbf{M}_{u^r}`.
            This is a graded coalgebra automorphism and an algebra
            anti-automorphism of `WQSym`.
            Denoting by `f^r` the image of an element `f \in WQSym`
            under the coalgebraic complement involution,
            it can be shown that every packed word `u` satisfies

            .. MATH::

                (\mathbf{M}_u)^r = \mathbf{M}_{u^r}, \qquad
                (X_u)^r = X_{u^r},

            where standard notations for classical bases of `WQSym`
            are being used (that is, `\mathbf{M}` for the monomial
            basis, and `X` for the characteristic basis).

            This can be restated in terms of ordered set partitions:
            For any ordered set partition `R` of `[n]`, let
            `\overline{R}` denote the complement of `R` (defined in
            :meth:`~sage.combinat.set_partition_ordered.OrderedSetPartition.complement`).
            Then,

            .. MATH::

                (\mathbf{M}_A)^r = \mathbf{M}_{\overline{A}}, \qquad
                (X_A)^r = X_{\overline{A}}

            for any ordered set partition `A`.

            Recall that `WQSym` is a subring of the ring of all
            bounded-degree noncommutative power series in countably many
            indeterminates. The latter ring has an obvious continuous
            algebra anti-endomorphism which sends each letter `x_i` to
            `x_i` (and thus sends each monomial
            `x_{i_1} x_{i_2} \cdots x_{i_n}` to
            `x_{i_n} x_{i_{n-1}} \cdots x_{i_1}`).
            This anti-endomorphism is actually an involution.
            The coalgebraic complement involution is simply the
            restriction of this involution to the subring `WQSym`.

            The formula describing coalgebraic complements on the Q basis
            (:class:`WordQuasiSymmetricFunctions.StronglyCoarser`)
            is more complicated, and requires some definitions.
            We define a partial order `\leq` on the set of all ordered
            set partitions as follows: `A \leq B` if and only if
            `A` is strongly finer than `B` (see
            :meth:`~sage.combinat.set_partition_ordered.OrderedSetPartition.is_strongly_finer`
            for a definition of this).
            The *length* `\ell(R)` of an ordered set partition `R` shall
            be defined as the number of parts of `R`.
            Use the notation `Q` for the Q basis.
            For any ordered set partition `A` of `[n]`, we have

            .. MATH::

                (Q_A)^r = \sum_P c_{A, P} Q_P ,

            where the sum is over all ordered set partitions `P` of
            `[n]`, and where the coefficient `c_{A, P}` is defined
            as follows:

            * If there exists an ordered set partition `R` satisfying
              `R \leq P` and `A \leq \overline{R}`, then this `R` is
              unique,
              and `c_{A, P} = \left(-1\right)^{\ell(R) - \ell(P)}`.

            * If there exists no such `R`, then `c_{A, P} = 0`.

            The formula describing coalgebraic complements on the `\Phi`
            basis (:class:`WordQuasiSymmetricFunctions.StronglyFiner`)
            is identical to the above formula for the Q basis, except
            that the `\leq` sign has to be replaced by `\geq` in the
            definition of the coefficients `c_{A, P}`. In fact, both
            formulas are particular cases of the general formula for
            involutions described in the documentation of
            :meth:`algebraic_complement`.

            If we let `\pi` be the canonical projection
            `WQSym \to QSym`, then each `f \in WQSym` satisfies
            `\pi(f^r) = \pi(f)`.

            .. SEEALSO::

                :meth:`algebraic_complement`, :meth:`star_involution`

            EXAMPLES:

            Recall that the index set for the bases of `WQSym` is
            given by ordered set partitions, not packed words.
            Translated into the language of ordered set partitions,
            the coalgebraic complement involution acts on the
            Monomial basis by complementing the ordered set partition.
            In other words, we have

            .. MATH::

                (\mathbf{M}_A)^r = \mathbf{M}_{\overline{A}}

            for any standard ordered set partition `P`.
            Let us check this in practice::

                sage: WQSym = algebras.WQSym(ZZ)
                sage: M = WQSym.M()
                sage: M[[1,3],[2]].coalgebraic_complement()
                M[{1, 3}, {2}]
                sage: M[[1,2],[3]].coalgebraic_complement()
                M[{2, 3}, {1}]
                sage: M[[1], [4], [2,3]].coalgebraic_complement()
                M[{4}, {1}, {2, 3}]
                sage: M[[1,4],[2,5],[3,6]].coalgebraic_complement()
                M[{3, 6}, {2, 5}, {1, 4}]
                sage: (3*M[[1]] - 4*M[[]] + 5*M[[1],[2]]).coalgebraic_complement()
                -4*M[] + 3*M[{1}] + 5*M[{2}, {1}]
                sage: X = WQSym.X()
                sage: X[[1,3],[2]].coalgebraic_complement()
                X[{1, 3}, {2}]
                sage: C = WQSym.C()
                sage: C[[1,3],[2]].coalgebraic_complement()
                C[{1, 3}, {2}]
                sage: Q = WQSym.Q()
                sage: Q[[1,2],[5,6],[3,4]].coalgebraic_complement()
                Q[{1, 2, 5, 6}, {3, 4}] + Q[{5, 6}, {1, 2}, {3, 4}] - Q[{5, 6}, {1, 2, 3, 4}]
                sage: Phi = WQSym.Phi()
                sage: Phi[[2], [1,3]].coalgebraic_complement()
                -Phi[{2}, {1}, {3}] + Phi[{2}, {1, 3}] + Phi[{2}, {3}, {1}]

            The coalgebraic complement involution intertwines the antipode
            and the inverse of the antipode::

                sage: all( M(I).antipode().coalgebraic_complement().antipode()  # long time
                ....:      == M(I).coalgebraic_complement()
                ....:      for I in OrderedSetPartitions(4) )
                True

            Testing the `\pi(f^r) = \pi(f)` relation above::

                sage: all( M[I].coalgebraic_complement().to_quasisymmetric_function()
                ....:      == M[I].to_quasisymmetric_function()
                ....:      for I in OrderedSetPartitions(4) )
                True

            .. TODO::

                Check further commutative squares.
            """
            # Convert to the Monomial basis, there apply the coalgebraic
            # complement componentwise, then convert back.
            parent = self.parent()
            M = parent.realization_of().M()
            dct = {I.complement(): coeff for (I, coeff) in M(self)}
            return parent(M._from_dict(dct, remove_zeros=False))

        def star_involution(self):
            r"""
            Return the image of the element ``self`` of `WQSym`
            under the star involution.

            The star involution is the composition of the
            algebraic complement involution
            (:meth:`algebraic_complement`) with the coalgebraic
            complement involution (:meth:`coalgebraic_complement`).
            The composition can be performed in either order, as the
            involutions commute.

            The star involution is a graded Hopf algebra
            anti-automorphism of `WQSym`.
            Let `f^{\ast}` denote the image of an element
            `f \in WQSym` under the star involution.
            Let `\mathbf{M}`, `X`, `Q` and `\Phi` stand for the
            monomial, characteristic, Q and Phi bases of `WQSym`.
            For any ordered set partition `A` of `[n]`, we let
            `A^{\ast}` denote the complement
            (:meth:`~sage.combinat.set_partition_ordered.OrderedSetPartition.complement`)
            of the reversal
            (:meth:`~sage.combinat.set_partition_ordered.OrderedSetPartition.reversed`)
            of `A`. Then, for any ordered set partition `A` of `[n]`,
            we have

            .. MATH::

                (\mathbf{M}_A)^{\ast} = \mathbf{M}_{A^{\ast}}, \qquad
                (X_A)^{\ast} = X_{A^{\ast}}, \qquad
                (Q_A)^{\ast} = Q_{A^{\ast}}, \qquad
                (\Phi_A)^{\ast} = \Phi_{A^{\ast}} .

            The star involution
            (:meth:`~sage.combinat.ncsf_qsym.ncsf.NonCommutativeSymmetricFunctions.Bases.ElementMethods.star_involution`)
            on the ring of noncommutative symmetric functions is a
            restriction of the star involution on `WQSym`.

            If we denote the star involution
            (:meth:`~sage.combinat.ncsf_qsym.qsym.QuasiSymmetricFunctions.Bases.ElementMethods.star_involution`)
            of the quasisymmetric functions by `f \mapsto f^{\ast}`,
            and if we let `\pi` be the canonical projection
            `WQSym \to QSym`, then each `f \in WQSym` satisfies
            `\pi(f^{\ast}) = (\pi(f))^{\ast}`.

            .. TODO::

                More commutative diagrams?
                FQSym and FSym need their own star_involution
                methods defined first.

            .. SEEALSO::

                :meth:`algebraic_complement`, :meth:`coalgebraic_complement`

            EXAMPLES:

            Keep in mind that the default input method for basis keys
            of `WQSym` is by entering an ordered set partition, not a
            packed word. Let us check the basis formulas for the
            star involution::

                sage: WQSym = algebras.WQSym(ZZ)
                sage: M = WQSym.M()
                sage: M[[1,3], [2,4,5]].star_involution()
                M[{1, 2, 4}, {3, 5}]
                sage: M[[1,3],[2]].star_involution()
                M[{2}, {1, 3}]
                sage: M[[1,4],[2,5],[3,6]].star_involution()
                M[{1, 4}, {2, 5}, {3, 6}]
                sage: (3*M[[1]] - 4*M[[]] + 5*M[[1],[2]]).star_involution()
                -4*M[] + 3*M[{1}] + 5*M[{1}, {2}]
                sage: X = WQSym.X()
                sage: X[[1,3],[2]].star_involution()
                X[{2}, {1, 3}]
                sage: C = WQSym.C()
                sage: C[[1,3],[2]].star_involution()
                -C[{1, 2, 3}] - C[{1, 3}, {2}] + C[{2}, {1, 3}]
                sage: Q = WQSym.Q()
                sage: Q[[1,3], [2,4,5]].star_involution()
                Q[{1, 2, 4}, {3, 5}]
                sage: Phi = WQSym.Phi()
                sage: Phi[[1,3], [2,4,5]].star_involution()
                Phi[{1, 2, 4}, {3, 5}]

            Testing the formulas for `(Q_A)^{\ast}` and `(\Phi_A)^{\ast}`::

                sage: all(Q[A].star_involution() == Q[A.complement().reversed()] for A in OrderedSetPartitions(4))
                True
                sage: all(Phi[A].star_involution() == Phi[A.complement().reversed()] for A in OrderedSetPartitions(4))
                True

            The star involution commutes with the antipode::

                sage: all( M(I).antipode().star_involution()  # long time
                ....:      == M(I).star_involution().antipode()
                ....:      for I in OrderedSetPartitions(4) )
                True

            Testing the `\pi(f^{\ast}) = (\pi(f))^{\ast}` relation::

                sage: all( M[I].star_involution().to_quasisymmetric_function()
                ....:      == M[I].to_quasisymmetric_function().star_involution()
                ....:      for I in OrderedSetPartitions(4) )
                True

            Testing the fact that the star involution on the
            noncommutative symmetric functions is a restriction of
            the star involution on `WQSym`::

                sage: NCSF = NonCommutativeSymmetricFunctions(QQ)
                sage: R = NCSF.R()
                sage: all(R[I].star_involution().to_fqsym().to_wqsym()
                ....:     == R[I].to_fqsym().to_wqsym().star_involution()
                ....:     for I in Compositions(4))
                True

            .. TODO::

                Check further commutative squares.
            """
            # Convert to the Monomial basis, there apply the algebraic
            # complement componentwise, then convert back.
            parent = self.parent()
            M = parent.realization_of().M()
            dct = {I.reversed().complement(): coeff for (I, coeff) in M(self)}
            return parent(M._from_dict(dct, remove_zeros=False))

        def to_quasisymmetric_function(self):
            r"""
            The projection of ``self`` to the ring `QSym` of
            quasisymmetric functions.

            There is a canonical projection `\pi : WQSym \to QSym`
            that sends every element `\mathbf{M}_P` of the monomial
            basis of `WQSym` to the monomial quasisymmetric function
            `M_c`, where `c` is the composition whose parts are the
            sizes of the blocks of `P`.
            This `\pi` is a ring homomorphism.

            OUTPUT:

            - an element of the quasisymmetric functions in the monomial basis

            EXAMPLES::

                sage: M = algebras.WQSym(QQ).M()
                sage: M[[1,3],[2]].to_quasisymmetric_function()
                M[2, 1]
                sage: (M[[1,3],[2]] + 3*M[[2,3],[1]] - M[[1,2,3],]).to_quasisymmetric_function()
                4*M[2, 1] - M[3]
                sage: X, Y = M[[1,3],[2]], M[[1,2,3],]
                sage: X.to_quasisymmetric_function() * Y.to_quasisymmetric_function() == (X*Y).to_quasisymmetric_function()
                True

                sage: C = algebras.WQSym(QQ).C()
                sage: C[[2,3],[1,4]].to_quasisymmetric_function() == M(C[[2,3],[1,4]]).to_quasisymmetric_function()
                True

                sage: C2 = algebras.WQSym(GF(2)).C()
                sage: C2[[1,2],[3,4]].to_quasisymmetric_function()
                M[2, 2]
                sage: C2[[2,3],[1,4]].to_quasisymmetric_function()
                M[4]
            """
            from sage.combinat.ncsf_qsym.qsym import QuasiSymmetricFunctions
            M = QuasiSymmetricFunctions(self.parent().base_ring()).Monomial()
            MW = self.parent().realization_of().M()
            return M.sum_of_terms((i.to_composition(), coeff)
                                  for (i, coeff) in MW(self))
