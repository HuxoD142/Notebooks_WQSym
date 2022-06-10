from sage.misc.latex import LatexExpr
from sage.combinat.words.words import Words

def tree_latex(self, colors=["red"]):
    r"""
    Generate `\LaTeX` output which can be easily modified.

    TESTS::

        sage: latex(BinaryTree([[[],[]],[[],None]]))
        { \newcommand{\nodea}{\node[draw,circle] (a) {$$}
        ;}\newcommand{\nodeb}{\node[draw,circle] (b) {$$}
        ;}\newcommand{\nodec}{\node[draw,circle] (c) {$$}
        ;}\newcommand{\noded}{\node[draw,circle] (d) {$$}
        ;}\newcommand{\nodee}{\node[draw,circle] (e) {$$}
        ;}\newcommand{\nodef}{\node[draw,circle] (f) {$$}
        ;}\begin{tikzpicture}[auto]
        \matrix[column sep=.3cm, row sep=.3cm,ampersand replacement=\&]{
                 \&         \&         \& \nodea  \&         \&         \&         \\
                 \& \nodeb  \&         \&         \&         \& \nodee  \&         \\
         \nodec  \&         \& \noded  \&         \& \nodef  \&         \&         \\
        };
        <BLANKLINE>
        \path[ultra thick, red] (b) edge (c) edge (d)
            (e) edge (f)
            (a) edge (b) edge (e);
        \end{tikzpicture}}
    sage: w = PackedWord([5,6,4,3,4,1,2,6])
    sage: view(tree_latex(w.packed_word_to_labelled_tree()))
    sage: view(tree_latex(w.packed_word_to_labelled_tree_left(),["blue"]))
    sage: view(tree_latex(w.packed_word_to_red_skeleton()))
    sage: view(tree_latex(w.packed_word_to_blue_skeleton(),["blue"]))
    sage: view(tree_latex(w.packed_word_to_red_skeleton(True),["black","red","blue"]))
    sage: view(tree_latex(w.packed_word_to_blue_skeleton(True),["black","blue","red"]))

    """
    ###############################################################################
    # # use to load tikz in the preamble (one for *view* and one for *notebook*)
    from sage.misc.latex import latex
    latex.add_package_to_preamble_if_available("tikz")
#    latex.add_to_mathjax_avoid_list("tikz")
    ###############################################################################
    # latex environnement : TikZ
    begin_env = "\\begin{tikzpicture}[auto]\n"
    end_env = "\\end{tikzpicture}"
    # it uses matrix trick to place each node
    matrix_begin = "\\matrix[column sep=.3cm,row sep=.3cm,ampersand replacement=\\&]{\n"
    matrix_end = "\\\\\n};\n"
    # a basic path to each edges
    paths_begin = []
    for color in colors:
        paths_begin+=["\\path[ultra thick,"+color+"] "]
    path_end = ";\n"
    # to make a pretty output, it creates one LaTeX command for
    # each node
    cmd = "\\node"
    new_cmd1 = "\\newcommand{" + cmd
    new_cmd2 = "}{\\node[draw,circle] ("
    new_cmd3 = ") {$"
    new_cmd4 = "$}\n;}"
    # some variables to simplify code
    sep = "\\&"
    space = " "*9
    sepspace = sep + space
    spacesep = space + sep

    def node_to_str(node):
        return " " + node + " " * (len(space) - 1 - len(node))
    # # TODO:: modify how to create nodes --> new_cmd : \\node[...] in create_node
    num = [0]

    def resolve(self):
        nodes = []
        matrix = []
        list_edges = [[] for _ in range(len(colors))]

        def create_node(self):
            r"""
            create a name (infixe reading)
             -> ex: b
            create a new command:
             -> ex: \newcommand{\nodeb}{\node[draw,circle] (b) {$$};
            return the name and the command to build:
              . the matrix
              . and the edges
            """
            name = "".join((chr(ord(x) + 49) for x in str(num[0])))
            node = cmd + name
            nodes.append((name,
                (str(self.label()[1]) if hasattr(self, "label") else ""))
            )
            num[0] += 1
            return node, name

        def empty_tree():
            r"""
            TESTS::

                sage: t = BinaryTree()
                sage: print(latex(t))
                { \begin{tikzpicture}[auto]
                \matrix[column sep=.3cm, row sep=.3cm,ampersand replacement=\&]{
                         \\
                };
                \end{tikzpicture}}
            """
            matrix.append(space)

        def one_node_tree(self):
            r"""
            TESTS::

                sage: t = BinaryTree([]); print(latex(t))
                { \newcommand{\nodea}{\node[draw,circle] (a) {$$}
                ;}\begin{tikzpicture}[auto]
                \matrix[column sep=.3cm, row sep=.3cm,ampersand replacement=\&]{
                 \nodea  \\
                };
                \end{tikzpicture}}
                sage: t = OrderedTree([]); print(latex(t))
                { \newcommand{\nodea}{\node[draw,circle] (a) {$$}
                ;}\begin{tikzpicture}[auto]
                \matrix[column sep=.3cm, row sep=.3cm,ampersand replacement=\&]{
                 \nodea  \\
                };
                \end{tikzpicture}}
            """
            node, _ = create_node(self)
            matrix.append(node_to_str(node))

        def concat_matrix(mat, mat2):
            lmat = len(mat)
            lmat2 = len(mat2)
            for i in range(max(lmat, lmat2)):
                # mat[i] --> n & n & ...
                # mat2[i] -> n' & n' & ...
                # ==> n & n & ... & n' & n' & ...
                try:
                    mat[i] += sep + mat2[i]
                except Exception:
                    if i >= lmat:
                        if i != 0:
                            # mat[i] does not exist but
                            # mat[0] has k "&"
                            # mat2[i] -> n' & n' & ...
                            # ==> (_ &)*k+1 n' & n' & ...
                            nb_of_and = mat[0].count(sep) - mat2[0].count(sep)
                            mat.append(spacesep * (nb_of_and) + mat2[i])
                        else:
                            # mat is empty
                            # mat2[i] -> n' & n' & ...
                            # ==> mat2
                            mat.extend(mat2)
                            return
                    else:
                        # mat[i] -> n & n & ...
                        # mat2[i] does not exist but mat2[0] exists
                        # # and has k "&"
                        # NOTE:: i != 0 because that is a no-empty subtree.
                        # ==> n & n & ... (& _)*k+1
                        nb_of_and = mat2[0].count(sep)
                        mat[i] += sepspace * (nb_of_and + 1)

        def tmp(subtree, edge, nodes, list_edges, matrix, side):
            # import pdb; pdb.set_trace()
            if not subtree.is_empty():
                # # create representation of the subtree
                nodes_st, matrix_st, list_edges_st = resolve(subtree)
                # # add its nodes to the "global" nodes set
                nodes.extend(nodes_st)
                # # build a new matrix by concatenation
                concat_matrix(matrix, matrix_st)
                if len(list_edges)==1:
                    # # add the subtree list_edges to the "global" list_edges set
                    list_edges[0].extend(list_edges_st[0])
                    # # create a new edge between the root and the subtree
                    edge.append(nodes_st[0][0])
                elif len(list_edges) == 2:
                    # # add the subtree list_edges to the "global" list_edges set
                    list_edges[0].extend(list_edges_st[0])
                    list_edges[1].extend(list_edges_st[1])
                    # # create a new edge between the root and the subtree
                    if side == "right":
                        list_edges[1].append([edge[0],nodes_st[0][0]])
                    else:
                        edge.append(nodes_st[0][0])
                elif len(list_edges)==3:
                    # # add the subtree list_edges to the "global" list_edges set
                    list_edges[0].extend(list_edges_st[0])
                    if side=="right":
                        list_edges[0].append([edge[0],nodes_st[0][0]])
                        # ici il faut rajouter dans list_edges[1 et 2] mais inversé
                        # (seulement si besoin)
                        list_edges[1].extend(list_edges_st[2])
                        list_edges[2].extend(list_edges_st[1])
                    else:
                        edge.append(nodes_st[0][0])
                        # # add the subtree list_edges to the "global" list_edges set
                        list_edges[1].extend(list_edges_st[1])
                        list_edges[2].extend(list_edges_st[2])
            else:
                concat_matrix(matrix, [space])

        def nodes_tree(self, nodes, list_edges, matrix):
            r"""
            TESTS::

                sage: t = OrderedTree([[[],[]],[[],[]]]).\
                ....:     canonical_labelling(); print(latex(t))
                { \newcommand{\nodea}{\node[draw,circle] (a) {$1$}
                ;}\newcommand{\nodeb}{\node[draw,circle] (b) {$2$}
                ;}\newcommand{\nodec}{\node[draw,circle] (c) {$3$}
                ;}\newcommand{\noded}{\node[draw,circle] (d) {$4$}
                ;}\newcommand{\nodee}{\node[draw,circle] (e) {$5$}
                ;}\newcommand{\nodef}{\node[draw,circle] (f) {$6$}
                ;}\newcommand{\nodeg}{\node[draw,circle] (g) {$7$}
                ;}\begin{tikzpicture}[auto]
                \matrix[column sep=.3cm, row sep=.3cm,ampersand replacement=\&]{
                         \&         \&         \& \nodea  \&         \&         \&         \\
                         \& \nodeb  \&         \&         \&         \& \nodee  \&         \\
                 \nodec  \&         \& \noded  \&         \& \nodef  \&         \& \nodeg  \\
                };
                <BLANKLINE>
                \path[ultra thick, red] (b) edge (c) edge (d)
                    (e) edge (f) edge (g)
                    (a) edge (b) edge (e);
                \end{tikzpicture}}
                sage: t = BinaryTree([[],[[],[]]]); print(latex(t))
                { \newcommand{\nodea}{\node[draw,circle] (a) {$$}
                ;}\newcommand{\nodeb}{\node[draw,circle] (b) {$$}
                ;}\newcommand{\nodec}{\node[draw,circle] (c) {$$}
                ;}\newcommand{\noded}{\node[draw,circle] (d) {$$}
                ;}\newcommand{\nodee}{\node[draw,circle] (e) {$$}
                ;}\begin{tikzpicture}[auto]
                \matrix[column sep=.3cm, row sep=.3cm,ampersand replacement=\&]{
                         \& \nodea  \&         \&         \&         \\
                 \nodeb  \&         \&         \& \nodec  \&         \\
                         \&         \& \noded  \&         \& \nodee  \\
                };
                <BLANKLINE>
                \path[ultra thick, red] (c) edge (d) edge (e)
                    (a) edge (b) edge (c);
                \end{tikzpicture}}
            """
            # import pdb; pdb.set_trace()
            # build all subtree matrices.
            node, name = create_node(self)
            edge = [name]
            split = self.label()[0]#len(self) // 2
            # the left part
            for i in range(split):
                tmp(self[i], edge, nodes, list_edges, matrix,"left")
            # # prepare the root line
            if len(matrix):
                nb_of_and = matrix[0].count(sep)
                sizetmp = len(matrix[0])
            else:
                nb_of_and = 0
                sizetmp = 0
            # the middle
            if len(matrix):
                for i in range(len(matrix)):
                    matrix[i] += sepspace
            else:
                for i in range(self.depth()-1):
                    matrix += [space + sepspace]
            # the right part
            for i in range(split, len(self)):
                tmp(self[i], edge, nodes, list_edges, matrix,"right")

            # # create the root line
            root_line = (spacesep * (nb_of_and + 1) + node_to_str(node) +
                sepspace * (matrix[0].count(sep) - nb_of_and - 1))
            matrix.insert(0, root_line)
            # add list_edges from the root
            if len(list_edges)==1:
                list_edges[0].append(edge)
            elif len(list_edges)==2:
                list_edges[0].append(edge)
            elif len(list_edges)==3:
                list_edges[1].append(edge)
                
        if self.is_empty():
            empty_tree()
        elif len(self) == 0 or all(subtree.is_empty()
                for subtree in self):
            one_node_tree(self)
        # elif len(self) % 2 == 0:
        #     pair_nodes_tree(self, nodes, list_edges, matrix)
        else:
            nodes_tree(self, nodes, list_edges, matrix)
        return nodes, matrix, list_edges

    nodes, matrix, list_edges = resolve(self)

    def make_cmd(nodes):
        cmds = []
        for name, label in nodes:
            cmds.append(new_cmd1 + name + new_cmd2 +
                name + new_cmd3 +
                label + new_cmd4)
        return cmds

    def make_edges(edges):
        all_paths = []
        for edge in edges:
            path = "(" + edge[0] + ")"
            for i in range(1, len(edge)):
                path += " edge (%s)" % edge[i]
            all_paths.append(path)
        return all_paths
    
    return LatexExpr("{ " +
        "".join(make_cmd(nodes)) +
        begin_env +
            (matrix_begin +
                "\\\\ \n".join(matrix) +
            matrix_end +
             ("\n".join([paths_begin[i] +
                         "\n\t".join(make_edges(list_edges[i])) +
                         path_end for i in range(len(list_edges))]))) +
            # path_begin +
            #     "\n\t".join(make_edges(edges)) +
            # path_end if len(edges) else "")
            # if len(matrix) else "") +
        end_env +
        "}")

"""
sage: for n in range(1,5):
....:     for p in PackedWords(n):
....:         better_tree_latex(p)
....:         better_tree_latex(p, "left")
....:         better_tree_latex(p, form = "ske")
....:         better_tree_latex(p, "left", "ske")
....:         better_tree_latex(p, form = "ske", bicolor=True)
....:         better_tree_latex(p, "left", "ske", bicolor=True)
sage: for p in PackedWords(5):
....:     if p.is_particular() and not p.is_particular("left"):
....:         better_tree_latex(p)
....:         better_tree_latex(p, "left")

sage: [better_tree_latex(p), better_tree_latex(p, "left"), better_tree_latex(p, form = "ske"), better_tree_latex(p, "left", "ske"), better_tree_latex(p, form = "ske", bicolor=True), better_tree_latex(p, "left", "ske", bicolor=True)]

  sage: WQSym = algebras.WQSym(QQ)
  sage: WQSym.inject_shorthands()
  sage: M.options.objects = 'words'
  sage: s = "$\\PP_{pp}$ & $\\PP_{\\scalebox{0.5}{\\input{figures/arbres_pw/arbrepp}}}$ & $\\OO_{\\scalebox{0.5}{\\input{figures/arbres_pw/arbreooleft}}}$ & $\\OO_{oo}$  \\\\ "

  sage: for p in PackedWords(5):
  ....:     if (p.is_particular() and not p.is_particular("left")) or (not p.is_particular() and p.is_particular("left")):
  ....:         print(s.replace("pp", str(Word(p))).replace("oo", str(O(P[p]).support()[0].to_packed_word())))
  ....:         print("\\hline")
  ....: 

"""
"""
un nouveau better_tree_latex pour les tables en annexes!
sage: n = 3
sage: for p in PackedWords(n):
....:     RR = str(R(P[p])).replace("R[","").replace("]","")
....:     PP = "\scalebox{0.5}{\input{figures/arbres_pw/arbreppske_bi}}".replace("pp",str(Word(p)))
....:     OO = "\scalebox{0.5}{\input{figures/arbres_pw/arbreooleftske_bi}}".replace("oo",str(O(P[p]).support()[0].to_packed_word()))
....:     QQ = str(Q(P[p])).replace("Q[","").replace("]","")
....:     print("\\hline")
....:     print("$",RR,"$ & $",PP,"$ & $",OO,"$ & $",QQ,"$\\\\")

"""


def better_tree_latex(pw, side = "", form = "", bicolor = False):
    """
    sage: better_tree_latex(PackedWord([2,3,1]))
    sage: better_tree_latex(PackedWord([1,2,2]),"left")
    sage: better_tree_latex(PackedWord([1,2,2]),form="ske")
    sage: better_tree_latex(PackedWord([1,2,2]),"left", "ske")
    sage: better_tree_latex(PackedWord([5,6,4,3,4,1,2,6]),form="ske")
    sage: better_tree_latex(PackedWord([5,6,4,3,4,1,2,6]),"left", "ske")
    sage: better_tree_latex(PackedWord([5,6,4,3,4,1,2,6]),form="ske", bicolor = True)
    sage: better_tree_latex(PackedWord([5,6,4,3,4,1,2,6]),"left", "ske", bicolor=True)
    sage: better_tree_latex(PackedWord([4,5,2,3,3,6,1,6]),form="ske")
    sage: better_tree_latex(PackedWord([4,5,2,3,3,6,1,6]),"left", "ske")
    sage: better_tree_latex(PackedWord([4,5,2,3,3,6,1,6]),form="ske", bicolor = True)
    sage: better_tree_latex(PackedWord([4,5,2,3,3,6,1,6]),"left", "ske", bicolor=True)
    sage: p = PackedWord([14,12,11,13,13,14,7,10,9,8,7,5,15,6,3,3,4,2,2,2,1,1,1,4,5])
    sage: better_tree_latex(PackedWord(p),form="ske", bicolor = True)
    sage: better_tree_latex(PackedWord(p),"left", "ske", True)
    sage: p = PackedWord([30,30,30,29,29,29,31,28,28,31,26,32,27, 22,25,24,23,22,20,19,18,20,21,21,26, 15,14,13,15,16,17,11,10,11,12,12,17, 8,6,7,7,8,4,3,3,1,5,2,1,9,9, 33])
    sage: better_tree_latex(PackedWord(p),form="ske", bicolor = True)
    sage: better_tree_latex(PackedWord(p),"left", "ske", True)
    sage: p = PackedWord([32,29,31,30,28,28,27,29,25,24,25,26,26,32, 22,20,21,21,22,23,17,16,18,18,19,23, 14,12,11,13,13,14,7,10,9,8,7,5,15,6,3,3,4,2,2,2,1,1,1,4,5, 33])
    sage: better_tree_latex(PackedWord(p),form="ske", bicolor = True)
    sage: better_tree_latex(PackedWord(p),"left", "ske", True)
    """
    assert(side in ["","right","left"] and form in ["","ske"])
#    load('~/recherche/opahc/perso/tree_latex.py')
    b = "_bi" if bicolor else ""
    name = "arbre"+str(Words()(pw))+side+form+b+".tex"
#    print(name)
    if form == "ske":
        if side == "left":
            l = str([tree_latex(t, ["blue","red"]) for t in
                     pw.packed_word_to_blue_skeleton_forest(bicolor)])
            # print(l)
            l = l[1:-1]
            l = l.replace("$[", "$")
            l = l.replace("]$", "$")
            l = l.replace(", ", "")
        else:
            l = str([tree_latex(t, ["red","blue"]) for t in
                     pw.packed_word_to_red_skeleton_forest(bicolor)])
            # print(l)
            l = l[1:-1]
            l = l.replace("$[", "$")
            l = l.replace("]$", "$")
            l = l.replace(", ", "")
    else:
        if side == "left":
            l = str([tree_latex(t,["blue"]) for t in pw.packed_word_to_labelled_forest_left()])
            # print(l)
            l = l[1:-1]
            l = l.replace(", True)", "^\\bullet")
            l = l.replace(", False)", "^\\circ")
            # l = l.replace("$(1^\\circ$", "")
            l = l.replace("$(", "$")
        else:
            l = str([tree_latex(t) for t in pw.packed_word_to_labelled_forest()])
            # print(l)
            l = l[1:-1]
            # l = l.replace("$[1]$", "")
            l = l.replace("$[", "$")
            l = l.replace("]$", "$")

#    l = l.replace("circle", "ellipse")
    l = l.replace("$1$","$\\,1\\,$")
    l = l.replace("$2$","$\\,2\\,$")
    l = l.replace("$3$","$\\,3\\,$")
    l = l.replace("$4$","$\\,4\\,$")
    l = l.replace("$5$","$\\,5\\,$")
    l = l.replace("$6$","$\\,6\\,$")
    l = l.replace("auto", "baseline={([yshift=-1ex]current bounding box.center)}")
    l = l.replace("}, {", "}\n{ ")

    # TODO essayer de faire ces savebox ici!!!...
    # l = l.replace("$[", "$")
    # l = l.replace("]$", "\\bullet$")
    # l = l.replace("$o$", "")
    return LatexExpr(l)
    print(l)
    fichier = open(name, 'w')
    fichier.write(l)
    fichier.close()
    return name

