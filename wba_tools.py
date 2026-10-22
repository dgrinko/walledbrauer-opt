from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.combinat.combinat_cython import perfect_matchings_iterator
from sage.combinat.set_partition import SetPartition
from sage.combinat.partition import Partition, Partitions
from sage.sets.set import Set

from sage.combinat.diagram_algebras import *
from sage.all import zero_vector, zero_matrix
from sage.rings.all import ZZ, NN, QQ

def walled_brauer_diagrams(p, q):
    k = p + q
    if k in ZZ:
        s = list(range(1,k+1)) + list(range(-k,0))
        for per in perfect_matchings_iterator(k):
            tmp = [(s[a],s[b]) for a,b in per]
            if all(not ((i[0]*i[1] > 0 and abs(i[0]) <= p and abs(i[1]) <= p) 
                        or (i[0]*i[1] > 0 and abs(i[0]) > p and abs(i[1]) > p) 
                        or (i[0]*i[1] < 0 and abs(i[0]) <= p and abs(i[1]) > p) 
                        or (i[0]*i[1] < 0 and abs(i[0]) > p and abs(i[1]) <= p)) for i in tmp):
                yield tmp
                
class WalledBrauerDiagram(BrauerDiagram):
    def __init__(self, parent, d, check=True):
        self.p = parent.p
        super(BrauerDiagram, self).__init__(parent, d, check=check)

    def check(self):
        # Validate the complete ground set as well as the size of each block.
        super().check()
        if len(self) != self.parent().order:
            raise ValueError("a diagram must contain p + q disjoint pairs")
        if any(((i[0]*i[1] > 0 and abs(i[0]) <= self.p and abs(i[1]) <= self.p) 
                        or (i[0]*i[1] > 0 and abs(i[0]) > self.p and abs(i[1]) > self.p) 
                        or (i[0]*i[1] < 0 and abs(i[0]) <= self.p and abs(i[1]) > self.p) 
                        or (i[0]*i[1] < 0 and abs(i[0]) > self.p and abs(i[1]) <= self.p)) for i in self):
            raise ValueError("all blocks of %s must be of walled type" % self)
            
class WalledBrauerDiagrams(BrauerDiagrams):
    Element = WalledBrauerDiagram
    options = WalledBrauerDiagram.options
    _name = "Walled Brauer"
    _diagram_func = walled_brauer_diagrams
    
    def __init__(self, p, q, category=None):
        if p not in NN or q not in NN:
            raise ValueError("walled Brauer ranks p and q must be nonnegative integers")
        if category is None:
            category = FiniteEnumeratedSets()
        Parent.__init__(self, category=category)
        self.p = ZZ(p)
        self.q = ZZ(q)
        self.order = self.p + self.q
        self._set = frozenset(list(range(1, self.order + 1))
                              + list(range(-self.order, 0)))
    
    def __contains__(self, obj):
        # The inherited shortcut accepts typed Brauer diagrams without checking
        # the wall. Reconstruct in this parent so every input is checked alike.
        try:
            self.element_class(self, obj, check=True)
        except (TypeError, ValueError):
            return False
        return True

    def cardinality(self):
        """Return (p + q)!, the number of walled Brauer diagrams."""
        return self.order.factorial()
    
    def __iter__(self):
        for i in self._diagram_func.__func__(self.p,self.q):
            yield self.element_class(self, i, check=False)

class WalledBrauerAlgebra(BrauerAlgebra):
    @staticmethod
    def __classcall_private__(cls, p, q, d, base_ring=None, prefix="B"):
        if base_ring is None:
            base_ring = d.parent()
        return super(WalledBrauerAlgebra, cls).__classcall__(cls, p, q, d, base_ring, prefix)
    
    def __init__(self, p, q, d, base_ring, prefix):
        SubPartitionAlgebra.__init__(self, p+q, d, base_ring, prefix, WalledBrauerDiagrams(p,q))  
        self.p = p
        self.q = q
        self.d = d
        
    def _repr_(self):
        return "Walled Brauer Algebra of rank ({},{}) with parameter {} over {}".format(
                self.p, self.q, self.d, self.base_ring())
    
    options = BrauerDiagram.options
    
    def _element_constructor_(self, set_partition):
        set_partition = SetPartition(to_Brauer_partition(set_partition, k=self.order()))
        return DiagramAlgebra._element_constructor_(self, set_partition)
    
    def jucys_murphy(self, j):
        """Return the Jucys--Murphy element with the contents of Sect. 5.3.

        At p = 0, use J_1 = delta * 1, the content of the first right
        addition. This resolves the overlapping k = 1 and k > p clauses
        in the published eq. (85).
        """
        if j < 1:
            raise ValueError("Jucys-Murphy index must be positive")
        k = self.order()
        if j > k:
            raise ValueError("Jucys-Murphy index cannot be greater than the order of the algebra")

        def convertI(x):
            return SetPartition(to_Brauer_partition(x, k=k))
        
        R = self.base_ring()
        one = R.one()
        diagrams = WalledBrauerDiagrams(self.p, self.q)
        coeffs = {self.one_basis(): R(self.d) if j > self.p else R.zero()}
        # _from_dict requires canonical basis indices, including the identity.
        for i in range(1, j):
            transposition = convertI([[i, -j], [j, -i]])
            contraction = convertI([[i, j], [-i, -j]])
            if transposition in diagrams:        # i, j on the same side of the wall
                coeffs[diagrams(transposition)] = one
            if contraction in diagrams:          # i, j on different sides of the wall
                coeffs[diagrams(contraction)] = -one
        return self._from_dict(coeffs, remove_zeros=True)
    


##############################################################
##############################################################

def vectorize_element_wb(v,lst,K):
    """Return coefficients in the requested diagram order, including for zero."""
    vec = zero_vector(K,len(lst))
    coefs_dict = v.monomial_coefficients()
    diagrams = v.parent().basis().keys()
    for i, diagram in enumerate(lst):
        vec[i] = coefs_dict.get(diagrams(diagram), 0)
    return vec

def psi_one_wb(diag,d,p,q,K):
    k = p+q
    mat=zero_matrix(K,d**k,sparse=True)
    index_range = [a for a in range(-k,0)] + [a for a in range(1,k+1)]
    
    i_j_dict = {key: None for key in index_range}
    for n in range(d**k):
        n_vec = NN(n).digits(d)
        n_vec.reverse()
        s=[0]
        while k-len(n_vec) !=0:
            n_vec=s+n_vec
            
        for m,pair in enumerate(diag):  
            i_j_dict[pair[0]] = n_vec[m]
            i_j_dict[pair[1]] = n_vec[m]

        row = ZZ([i_j_dict[k-i+1] for i in range(1,k+1)], base=d)    # top row = bra, eq. (44)
        col = ZZ([i_j_dict[-k+i-1] for i in range(1,k+1)], base=d)   # bottom row = ket
        mat[row,col] = 1
    return mat

def psi_wb(v,d,p,q,K):      
    lst=WalledBrauerDiagrams(p,q).list()
    vec=vectorize_element_wb(v,lst,K)
    mat=zero_matrix(K,d**(p+q),sparse=True)
    
    for i in range(len(lst)):
        if vec[i]!=0:
            mat += vec[i] * psi_one_wb(lst[i],d,p,q,K)
    return mat

def lambda_mu_content(Lambda,Mu,level_p,z):  
    L=Set(Mu[0].cells())
    R=Set(Mu[1].cells())  
    
    L_prev=Set(Lambda[0].cells())
    R_prev=Set(Lambda[1].cells())
        
    if level_p:
        if Mu[0].size()>Lambda[0].size():
            tmp=L.difference(L_prev)
            return ZZ(tmp[0][1]-tmp[0][0])
        raise ValueError("This is not a valid edge")
    else:
        if Mu[0].size()<Lambda[0].size():
            tmp=L_prev.difference(L)
            return -ZZ(tmp[0][1]-tmp[0][0])
        elif Mu[1].size()>Lambda[1].size():
            tmp=R.difference(R_prev)
            return ZZ(tmp[0][1]-tmp[0][0])+z
        else:
            raise ValueError("This is not a valid edge")
            
def walled_brauer_irreducibles(p,q): 
    lst=[]
    for i in range(0,min(p,q)+1):
        for x in Partitions(p-i):
            for y in Partitions(q-i):
                lst = lst + [tuple([x,y])]
    return lst

def bratteli_antecedents(Lambda,p,q):
    lst=[]
    if q>=1:
        if Lambda[1].size()+Lambda[0].size()!= p+q:
            for x in Lambda[0].addable_cells():
                tmp = Lambda[0].add_cell(x[0])
                lst += [tuple([tmp,Lambda[1]])]
                
            for x in Lambda[1].removable_cells():
                tmp = Lambda[1].remove_cell(x[0])
                lst += [tuple([Lambda[0],tmp])]
        else:
            for x in Lambda[1].removable_cells():
                tmp = Lambda[1].remove_cell(x[0])
                lst += [tuple([Lambda[0],tmp])]
    else:
        for x in Lambda[0].removable_cells():
            tmp = Lambda[0].remove_cell(x[0])
            lst += [tuple([tmp,Lambda[1]])]
       
    return lst

def bratteli_descendants(Mu,level_p):
    lst=[]
    if level_p:
        for x in Mu[0].addable_cells():
            lst += [tuple([Mu[0].add_cell(x[0]), Mu[1]])]
    else:
        for x in Mu[1].addable_cells():
            lst += [tuple([Mu[0], Mu[1].add_cell(x[0])])]
        for x in Mu[0].removable_cells():
            lst += [tuple([Mu[0].remove_cell(x[0]), Mu[1]])]
    return lst
      
def gelfand_tsetlin_basis(Mu,p,q):
    k = p+q
    GT_basis = [[Mu]]
    while k >= 1:
        if k > p:
            pk, qk = p, k-p
        else: 
            pk, qk = k, 0
        
        GT_basis_new = []
        for path in GT_basis:
            GT_basis_path = []
            for Lambda in bratteli_antecedents(path[-1],pk,qk):
                GT_basis_path.append(path+[Lambda])
            GT_basis_new += GT_basis_path
        GT_basis = GT_basis_new
        k -= 1
        
    for x in GT_basis:
        x.reverse()

    return GT_basis

def interpolating_polynomial_lambda_mu(elem,Lambda,Mu,p,q,z,K,level_p):
    iden=WalledBrauerAlgebra(p,q,z,K).one()
    val=iden
    
    c_T = lambda_mu_content(Lambda,Mu,level_p,z)
    for x in bratteli_descendants(Lambda,level_p):
        if x!=Mu:
            c_S=lambda_mu_content(Lambda,x,level_p,z)
            new_val=(elem-c_S*iden)*(K(1/(c_T-c_S))*iden)
            val=val*new_val
    return val

##############################################################
##############################################################

def walled_brauer_irreducibles_d(p,q,d): 
    lst=[]
    for i in range(0,min(p,q)+1):
        for x in Partitions(p-i):
            for y in Partitions(q-i):
                if len(x)+len(y) <= d:
                    lst = lst + [tuple([x,y])]
    return lst

def bratteli_antecedents_d(Lambda,p,q,d):
    lst=[]
    if q>=1:
        if Lambda[1].size()+Lambda[0].size()!= p+q:
            for x in Lambda[0].addable_cells():
                tmp = Lambda[0].add_cell(x[0])
                if len(tmp)+len(Lambda[1]) <= d:
                    lst += [tuple([tmp,Lambda[1]])]
                
            for x in Lambda[1].removable_cells():
                tmp = Lambda[1].remove_cell(x[0])
                if len(tmp)+len(Lambda[0]) <= d:
                    lst += [tuple([Lambda[0],tmp])]
        else:
            for x in Lambda[1].removable_cells():
                tmp = Lambda[1].remove_cell(x[0])
                if len(tmp)+len(Lambda[0]) <= d:
                    lst += [tuple([Lambda[0],tmp])]
    else:
        for x in Lambda[0].removable_cells():
            tmp = Lambda[0].remove_cell(x[0])
            if len(tmp)+len(Lambda[1]) <= d:
                lst += [tuple([tmp,Lambda[1]])]
       
    return lst

def bratteli_descendants_d(Mu,level_p,d):
    lst=[]
    if level_p:
        for x in Mu[0].addable_cells():
            tmp = tuple([Mu[0].add_cell(x[0]), Mu[1]])
            if len(tmp[0]) + len(tmp[1]) <= d:
                lst += [tmp]
    else:
        for x in Mu[1].addable_cells():
            tmp = tuple([Mu[0], Mu[1].add_cell(x[0])])
            if len(tmp[0]) + len(tmp[1]) <= d:
                lst += [tmp]
        for x in Mu[0].removable_cells():
            tmp = tuple([Mu[0].remove_cell(x[0]), Mu[1]])
            if len(tmp[0]) + len(tmp[1]) <= d:
                lst += [tmp]
    return lst
    
def gelfand_tsetlin_basis_d(Mu,p,q,d):
    k = p+q
    GT_basis = [[Mu]]
    while k >= 1:
        if k > p:
            pk, qk = p, k-p
        else: 
            pk, qk = k, 0
        
        GT_basis_new = []
        for path in GT_basis:
            GT_basis_path = []
            for Lambda in bratteli_antecedents_d(path[-1],pk,qk,d):
                GT_basis_path.append(path+[Lambda])
            GT_basis_new += GT_basis_path
        GT_basis = GT_basis_new
        k -= 1
        
    for x in GT_basis:
        x.reverse()

    return GT_basis

def interpolating_polynomial_lambda_mu_d(elem,Lambda,Mu,p,q,d,K,level_p):
    iden=WalledBrauerAlgebra(p,q,d,K).one()
    val=iden
    c_T = lambda_mu_content(Lambda,Mu,level_p,ZZ(d))
    for x in bratteli_descendants_d(Lambda,level_p,d): 
        if x!=Mu:
            c_S=lambda_mu_content(Lambda,x,level_p,ZZ(d))
            new_val=(elem-c_S*iden)*QQ(1/(c_T-c_S))
            val=val*new_val
    return val
