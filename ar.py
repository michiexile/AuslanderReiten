import networkx as nx
from collections import deque

"""
Note, due to the algorithms in nx, this will only work for
DAG quivers; however: if the quiver is not DAG we cannot
expect it to have finitely many indecomposables anyway.
"""


def findsublist(haystack, needle):
    """
    Boyer-Moore-Horspool algorithm
    taken from http://codereview.stackexchange.com/questions/19627/finding-sub-list
    """
    h = len(haystack)
    n = len(needle)
    skip = {needle[i]: n - i - 1 for i in range(n - 1)}
    i = n - 1
    while i < h:
        for j in range(n):
            if haystack[i - j] != needle[-j - 1]:
                i += skip.get(haystack[i], n)
                break
        else:
            return i - n + 1
    return -1
    

class Quiver (nx.MultiDiGraph):
    """
    Class for a Quiver. A quiver is basically a multi-digraph, but we
    may want to work with dimension vectors for modules over the
    quiver -- and these will depend on a chosen ordering for the nodes.
    So we make this functionality intrinsic to the Quiver class.
    """
    
    def __init__(self):
        nx.MultiDiGraph.__init__(self)
        self.api = None
        self.aii = None
        self.ari = None
        self.rel = {}
        self.comm = False

        
    def add_relation(self, path0, path1):
        """
        Insert a re-writing relation for paths in the quiver.
        This is how we represent (simple) relations in the Path algebra.
        Better but more ambitious would be to instead use a Grobner approach.

        The user has to provide a consistent set of re-writing relations.
        """
        self.rel[path0] = path1

    def applyRelations(self, p):
        """
        Apply the stored re-writing relations to a given path p.
        """
        stop = False
        ret = p
        while not stop:
            stop = True
            for r in self.rel:
                pos = findsublist(list(ret), list(r))
                if pos >= 0:
                    ret = list(self.rel[r]) + list(p[pos+len(r):])
                    stop = False
        return tuple(ret)

    def listPaths(self, s, t):
        """
        Recursively list all paths in the quiver that go from s to t.
        These are _all_ paths, not representatives for equivalence classes.
        """
        if s == t:
            return [[t]]
        return [[s]+p for ss in self.successors(s) for p in self.listPaths(ss,t)]

    def listReducedPaths(self, s, t):
        """
        List all paths in the quiver from s to t: up to the equivalences
        in the relations of the quiver.
        """
        paths = self.listPaths(s,t)
        red = {self.applyRelations(p) for p in paths}
        return list(red)

    def countReducedPaths(self, s, t):
        """
        Count the number of eqiuvalence classes of paths from s to t.
        """
        npaths = len(self.listReducedPaths(s,t))
        if self.comm:
            if npaths == 0:
                return 0
            else:
                return 1
        return npaths
    
    def proj_indecomp(self,v):
        """
        Compute the projective indecomposable of the vertex v.
        If a cached result exists, use that instead.
        """
        if self.api:
            return self.api[self.nodes().index(v)]
        return tuple([self.countReducedPaths(v, w) for w in self.nodes()])

    def inj_indecomp(self,v):
        """
        Compute the injective indecomposable of the vertex v.
        If a cached result exists, use that instead.
        """
        if self.aii:
            return self.aii[self.nodes().index(v)]
        return tuple([self.countReducedPaths(w,v) for w in self.nodes()])

    def radical_proj(self, v):
        """
        Compute the radical of the projective indecomposable of the vertex v.
        If a cached result exists, use that instead.
        """
        if self.ari:
            return self.ari[self.nodes().index(v)]
        proj = list(self.proj_indecomp(v))
        proj[self.nodes().index(v)] = 0
        return tuple(proj)

    def all_proj_indecomp(self):
        """
        Compute and cache a list of all projective indecomposables.
        """
        if not self.api:
            self.api = [self.proj_indecomp(v) for v in self.nodes()]
        return self.api

    def all_rad_indecomp(self):
        """
        Compute and cache a list of all radicals of projective indecomposables.
        """
        if not self.ari:
            self.ari = [self.radical_proj(v) for v in self.nodes()]
        return self.ari
    
    def all_inj_indecomp(self):
        """
        Compute and cache a list of all injective indecomposables.
        """
        if not self.aii:
            self.aii = [self.inj_indecomp(v) for v in self.nodes()]
        return self.aii

    def isSimple(self, module):
        """
        Check whether a dimension vector describes a simple module.
        """
        return sum(module) == 1 and len([m for m in module if m != 0]) == 1
    
    def zeros(self):
        """
        Returns the zero module.
        """
        return tuple([0 for v in self.nodes()])

    """
    Example usage:
Q = Quiver()
Q.add_edge(1,2)
Q.add_edge(3,2)
Q.add_edge(4,5)
Q.add_edge(6,5)
Q.add_edge(1,4)
Q.add_edge(2,5)
Q.add_edge(3,6)
Q.add_relation((1,2,5),(1,4,5))
Q.add_relation((3,2,5),(3,6,5))
ar = arQuiver(Q)
"""

def arQuiver(G):
    """
    Compute the Auslander-Reiten quiver of G by repeatedly finding
    almost split short exact sequences.
    """
    ar = Quiver()
    todo = deque()

    for v in G.nodes():
        ar.add_edge(G.radical_proj(v), G.proj_indecomp(v))
        ar.add_node(G.inj_indecomp(v))
        if G.isSimple(G.proj_indecomp(v)):
            todo.append(G.proj_indecomp(v))

    ar.remove_node(G.zeros())

    ctr = 0
    while len(todo) > 0:
        ctr += 1
        if ctr % 10 == 0:
            print ctr, todo

        p = todo.popleft()

        if G.isSimple(p) and p in G.all_inj_indecomp():
            continue
        ss = ar.successors(p)
        w = tuple([sum([s[j] for s in ss])-p[j] for j in range(len(p))])
        if len([wv for wv in w if wv < 0]) > 0:
            continue
        if len([wv for wv in w if wv >= 7]) > 0:
            print "Infinite representation!"
            return ar
        for s in ss:
            ar.add_edge(s,w)
            if s not in todo:
                todo.append(s)
    return ar

        

Q = Quiver()
Q.comm = True

Q.add_edge(1,2)
Q.add_edge(3,2)
Q.add_edge(4,3)
Q.add_edge(1,5)
Q.add_edge(2,6)
Q.add_edge(3,7)
Q.add_edge(4,8)
Q.add_edge(5,6)
Q.add_edge(7,6)
Q.add_edge(8,7)
