#######################################################################################
# Algebraic Starscapes code                                                           #
# Edmund Harriss, Kate Stange, Steve Trettel and Pierre Arnoux                        #
#######################################################################################

# This provides functions to generate images, primarily of algebraic numbers as 
# collections of differently sized dots. 
# Images are constructed in three phases:
# 1) Create a list of polynomials, as lists themselves
# 2) Process the data on the polynomials into geometric information, position, size and colour
# 3) Draw the resulting image
# A final section provides some simpler functions for common tasks and a function to output images

from abc import ABC, abstractmethod
import matplotlib.pyplot as plt
import time
import itertools
from matplotlib.patches import Circle, Polygon
import numpy as np

# Section 1: create lists of polynomials (as a list of values)

def absSum(p):
    t = 0
    for i in p:
        t=t+abs(i)
    return t

# all polynomials above a certain degree (minD) with absolute coefficient total up to n
def upTo(n, minD=None, maxD=None):
    if minD == None: 
        minD = 2
    if maxD == None:
        maxD = n
    level = [[a] for a in range(-n,n+1)]
    all = []
    if minD == 0:
        all = level
    for l in range(maxD) :
        newlevel = []
        for p in level:
            sofar = absSum(p)
            for newv in range(-n+sofar,n-sofar+1):
                tempP = p.copy()
                tempP.append(newv)
                newlevel.append(tempP)
        level = newlevel
        if(l >= minD - 1):
            all = all + level
    all = [p for p in all if p[-1]>0] # ensure leading coefficient is positive leaving out smaller polynomials and the identical negative equation.
    return all

# 2d, 3d or 4d family of polynomials

def polyRange(pol,arange,brange,crange=None,drange=None, coprime=True):
    pts = []
    if crange==None:
        for a in arange:
            for b in brange:
                if not coprime or gcd([a,b]) == 1:
                    f = pol(a,b)
                    pts.append(f.list())
    elif drange==None:
        for a in arange:
            for b in brange:
                for c in crange:
                    if not coprime or gcd([a,b,c]) == 1:
                        f = pol(a,b,c)
                        pts.append(f.list())
    else:
        for a in arange:
            for b in brange:
                for c in crange:
                    for d in drange:
                        if not coprime or gcd([a,b,c,d]) == 1:
                            f = pol(a,b,c,d)
                            pts.append(f.list())
    return pts

# Add the reverse of a polynomial to make reciprocal polynomials.

def reciprocal(l, even=True, odd=True):
    pts = []
    for p in l:
        rp = p.copy()
        rp.reverse()
        if even: pts.append(p+rp)
        rp.pop(0)
        if odd: pts.append(p+rp)
    return pts
    
# Spread a collection of polynomials over Sl2Z
# TODO currently only handles quadratics and cubics, make general
def polyCoeffAdd(p, n):
    if len(p) == 3:
        return [p[0]-n*p[1]+n**2*p[2],p[1]-n*2*p[2],p[2]]
    elif len(p) == 4:
        return [p[0]-n*p[1]+n**2*p[2]-n**3*p[3],p[1]-2*n*p[2]+3*n**2*p[3],p[2]-3*n*p[3],p[3]]
    else:
        return p

def polyCoeffNegInv(p):
    pc = p.copy()
    pc.reverse()
    pc = [(-1)**i*pc[i] for i in range(len(pc))]
    return pc
    
def nodup(l):
    ls = sorted(l)
    return [i for i, _ in itertools.groupby(ls)]

def SL2Z(l, s):
    newl = l
    extra = l + [polyCoeffNegInv(p) for p in l]
    extra = nodup(extra)
    for i in range(s):
        extra = [polyCoeffAdd(p,-1) for p in extra] + [polyCoeffAdd(p,1) for p in extra]
        extra = extra + [polyCoeffNegInv(p) for p in extra]
        extra = nodup(extra)
        newl = newl+extra
        newl = nodup(newl)
    return newl
        
        
# Section 2: Converting the data into geometry

# convert list of polynomials (as list of entries) to data about roots.
# each root gets the following information:
#  [polynomial (as list units coefficient first), 
#  root as (real part, imaginary part), 
#  degree of root
#  all roots of polynomial,  
#  global height, 
#  discriminant]

class rtData:
    def __init__ (self, poly, rt, degree, rts, height, disc):
        self.poly = poly
        self.rt = rt
        self.degree = degree
        self.rts = rts
        self.height = height
        self.disc = disc

def onUnitCircle(p):
    eps = .0000000001
    av = p[0]^2+p[1]^2
    return av > 1-eps and av < 1+eps

def rootData(l, height=False, degree=True, minimal=False, unitCircle=True, coprime=True):
    pts = []
    for p in l:
        if not coprime or gcd(p) == 1:
            f = P(p)
            disc = f.discriminant()
            if not degree or (f.is_irreducible() and (not minimal or p[-1] != 0)):
                rts = f.roots(CC)
                for rt in rts:
                    re = RR(rt[0].real())
                    im = RR(rt[0].imag())
                    if 0 < im and (not onUnitCircle((re,im)) or unitCircle):
                        pt = rtData(f, (re,im), f.degree(), rts, 0, disc)
                        if height:
                            F.<alpha> = NumberField(f)
                            pt.height = alpha.global_height()
                        pts.append(pt)
            elif not minimal:
                if f != 0:
                    rts = f.roots(QQbar)
                    for rt in rts:
                        re = RR(rt[0].real())
                        im = RR(rt[0].imag())
                        if 0 < im and (not onUnitCircle((re,im)) or unitCircle):
                            pt = rtData(f, (re,im), rt[0].degree(), rts, 0, disc)
                            pts.append(pt)
                
    print("rootData created a list of "+str(len(pts))+" points")
    return pts

# create data for first two real roots
def realRoots(l, height=False, degree=True, minimal=False, coprime=True):
    pts = []
    for p in l:
        if not coprime or gcd(p) == 1:
            f = P(p)
            disc = f.discriminant()
            if not degree or (f.is_irreducible() and (not minimal or p[-1] != 0)): 
                rts = f.roots(CC)
                rrts = []
                for rt in rts:
                    re = RR(rt[0].real())
                    im = RR(rt[0].imag())
                    if 0 == im:
                        rrts.append(re)
                if(len(rrts)>1):
                    pt = rtData(f, (rrts[0],rrts[1]), f.degree(), rts, 0, disc)
                    if height:
                        F.<alpha> = NumberField(f)
                        pt.height = alpha.global_height()
                    pts.append(pt)
            elif not minimal:
                if f != 0:
                    rts = f.roots(QQbar)
                    rrts = []
                    for rt in rts:
                        re = RR(rt[0].real())
                        im = RR(rt[0].imag())
                        if 0 == im:
                            rrts.append(re)
                    if(len(rrts)>1):
                        pt = rtData(f, (rrts[0],rrts[1]), f.degree(), rts, 0, disc)
                        pts.append(pt)                
    print("realRoots created a list of "+str(len(pts))+" points")
    return pts

# Create a list of rationals using height to store the denominator
def rationals(arange, brange, crange):
    pts = []
    for a in arange:
        for b in brange:
            for c in crange:
                pt = rtData(P([a,b,c]), (b/a,c/a), 1, [], a, 0)   
                pts.append(pt)
    print("rationals created a list of "+str(len(pts))+" points")
    return pts
    
####################################
# Functions to select points (Rather limited at present)
####################################


# Lower central unit cell for the modular surface. (or translations of it (in x) by t)

def inUCell1(rt,t):
    return (vector(rt.rt)-vector([t,0])).norm() < 1 and (vector(rt.rt)-vector([t+1,0])).norm() > 1 and (vector(rt.rt)-vector([t-1,0])).norm() > 1 
        
# cell to the lower right of it

def inUCell2(rt,t):
    return (vector(rt.rt)-vector([t+1,0])).norm() < 1 and (rt.rt[0]-t) < .5 and (vector(rt.rt)-vector([t+1/3,0])).norm() > 1/3 

def inRegion(L, regionFun=inUCell1, t=0):
    return [l for l in L if regionFun(l,t)]
    

####################################
# Sizing functions
####################################

def height(rt): 
    return 1.0/exp(rt.height)^(rt.degree)
def disc(rt): 
    return 1.0/abs(rt.disc)
def rootDisc(rt):
    return 1.0/abs(rt.disc)^(1/rt.poly.degree())
def mahler(rt):
    mm=abs(rt.poly.list()[-1])
    for r in rt.rts:
        mm = mm*max(1,abs(r[0])^r[1])
    return 1.0/mm
def oneNorm(rt):
    return 1.0/absSum(rt.poly.list())
def inftyNorm(rt):
    return 1.0/max([abs(i) for i in rt.poly.list()])
def twoNorm(rt):
    return 1.0/vector(rt.poly.list()).norm()
def leadCoeff(rt):
    return 1.0/rt.poly.list()[-1]
def rational(rt):
    return 1.0/rt.height
    
# Normalized sizings

def Nheight(rt):
    return height(rt)**((rt.degree+1)/2)

def Ndisc(rt):
    return disc(rt)**((rt.degree+1)/(4*(rt.degree-1)))

def NinftyNorm(rt):
    return inftyNorm(rt)**((rt.degree+1)/2.0)
    
def Nmahler(rt):
    return mahler(rt)**((rt.degree+1)/2.0)
    
    
    


####################################
# Shape functions
####################################

def circ(rt, sizefun, colfun):
    return dotData(rt.rt, sizefun(rt), colfun(rt))
    
def tanBundleArrow(rt, sizefun, colfun):
    rr = None;
    d = (0,0)
    for i in rt.rts:
        if imag(i[0]) == 0: 
            rr = real(i[0])
            break
    if rr == None: 
        d = (0,1)
    else:
        x = rt.rt[0]
        y = rt.rt[1]
        d = ((rr-x)*y,(rr-x)**2-y**2)
        l = sqrt(d[0]**2+d[1]**2)
        d = (d[0]/l, d[1]/l)
    return arrowData(rt.rt, d, sizefun(rt), colfun(rt))
    

####################################
# Colouring functions
####################################

# Colours for degree, starting at degree 0.
dCols = [(0,0,0,1), (0,0,0,1), (0,0,0,1), (.95,.15,.2,1), (.2,.15,1,1), (.7,.4,1,1)]
# Colours for number of real roots, starting at 0.
rrCols = [(0,0,0,1), (0,0,0,1), (0,0,0,1), (.95,.15,.2,1), (.2,.15,1,1), (.7,.4,1,1)]

def col(c): return lambda rt: c

def degCol(rt): 
    if rt.degree < len(dCols):
        return dCols[rt.degree]
    else:
        return (.7,.7,.7,1)
    
def degColRootDisc(rt): 
    if rt.degree < len(dCols):
        s = (1-2.0/RR(abs(rt.disc)^(1/rt.poly.degree())))
        col = [.9*s*s+i*(1-s*s) for i in dCols[rt.degree]]
        col[3] = 1
        return tuple(col)
    else:
        return (.7,.7,.7,1)
# Colour by first real root 
    # red for negative, 
    # blue for positive, 
    # black for 0
    # gray for no real root
def realRootCol(rt): 
    rr = None;
    e = 2.;
    if(rt.degree == 2):
        return (0,0,0,1)
    for i in rt.rts:
        if imag(i[0]) == 0: 
            rr = real(i[0])
            break
    if rr == None: 
        return (.5,.5,.5,1)
    if rr == 0: 
        return (0,0,0,1)
    elif rr < 0:
        return (1,1-e^(rr),1-e^(rr),1)
    return (1-e^(-rr),1-e^(-rr),1)
# Variation where positive reals make things fade faster
def realRootCol_fadepos(rt): 
    rr = None;
    e = 2.;
    for i in rt.rts:
        if imag(i[0]) == 0: 
            rr = real(i[0])
            break
    if rr == None: 
        return (.5,.5,.5,1)
    if rr == 0: 
        return (0,0,0,1)
    elif rr < 0:
        return (1,1-e^(rr),1-e^(rr),1)
    return (1-e^(-3*rr),1-e^(-3*rr),1)
    
# Colour by the number of real roots using the same colouring as degree, 
# with 0 real roots given the colour for degree 2, and increasing from there. 
def realRootCount(rt):
    rr = 0;
    e = 2.;
    for i in rt.rts:
        if imag(i[0]) == 0: 
            rr = rr+1
    if rr < len(rrCols):
        return rrCols[rr]
    else:
        return (.7,.7,.7,1)
        
    
def normDiscRatio(rt): 
    if rt.degree < len(dCols):
        s = (1.57+atan(log(absSum(rt.poly.list())/RR(abs(rt.disc)^(1/rt.poly.degree())))))/3.14
        col = (s,0,1-s,1)
        return col
    else:
        return (.7,.7,.7,1)

# Show everything in the quadratic colour and the Salem numbers in the cubic colour
def seeSalem(rt):
    g1rts = 0 # number of roots outside unit circle
    for i in rt.rts:
        if abs(i[0]) > 1: 
            g1rts = g1rts+1
    if g1rts > 1: # not Salem
        return dCols[2]
    else:
        return dCols[3]

####################################
# Drawing class, allowing for drawing on Euclidean plane or hyperbolic upperhalf plane. 
####################################

class drawData(ABC):
    @abstractmethod
    def drawH(self):
        pass
    @abstractmethod
    def drawE(self):
        pass

class dotData(drawData):
    def __init__(self, pt, radius, colour):
        self.pt = vector(pt)
        self.radius = radius
        self.colour = colour
        
    def drawH(self, ax, scaling, xlims, ylims, line, edgeCol):
        if self.pt[0]>=xlims[0] and self.pt[0]<=xlims[1] and self.pt[1]>=ylims[0] and self.pt[1]<=ylims[1]:
            ax.add_artist(Circle(xy=(self.pt[0], self.pt[1]*cosh(scaling*self.radius)),
                            radius=self.pt[1]*sinh(scaling*self.radius), 
                            ec=edgeCol, fc=self.colour, lw=line))
            return 1
        return 0
        
    def drawE(self, ax, scaling, xlims, ylims, line, edgeCol):
        if self.pt[0]>=xlims[0] and self.pt[0]<=xlims[1] and self.pt[1]>=ylims[0] and self.pt[1]<=ylims[1]:
            ax.add_artist(Circle(xy=self.pt,
                radius=scaling*self.radius,
                ec=edgeCol, fc=self.colour, lw=line))
            return 1
        return 0
        
        
rt3 = 1.7320508
class arrowData(drawData):
    
    def __init__(self, pt, d, radius, colour):
        self.pt = vector(pt)
        self.d = vector(d)
        self.radius = radius
        self.colour = colour
        
        
    def drawH(self, ax, scaling, xlims, ylims, line, edgeCol):
        if self.pt[0]>=xlims[0] and self.pt[0]<=xlims[1] and self.pt[1]>=ylims[0] and self.pt[1]<=ylims[1]:
            dp = vector([self.d[1],-1*self.d[0]]) # Perpendicular vector
            ax.add_artist(Polygon([
                self.pt+scaling*self.pt[1]*self.radius*rt3*self.d, 
                self.pt+scaling*self.pt[1]*self.radius*dp/2, 
                self.pt-scaling*self.pt[1]*self.radius*((rt3*self.d-dp)/4), 
                self.pt-scaling*self.pt[1]*self.radius*((rt3*self.d+dp)/4),
                self.pt-scaling*self.pt[1]*self.radius*dp/2,
                self.pt+scaling*self.pt[1]*self.radius*rt3*self.d], 
                True, ec=edgeCol, fc=self.colour, lw=line))
            return 1
        return 0
        
    def drawE(self, ax, xlims, ylims, line, edgeCol):
        
        if self.pt[0]>=xlims[0] and self.pt[0]<=xlims[1] and self.pt[1]>=ylims[0] and self.pt[1]<=ylims[1]:
            dirp = [self.dir[1],-self.dir[0]] # Perpendicular vector
            ax.add_artist(Polygon([
                self.pt+self.radius*self.dir, 
                self.pt-self.radius*(self.dir+dirp/4), 
                self.pt-self.radius*(self.dir-dirp/4),
                self.pt+self.radius*self.dir], True,
                ec=edgeCol, fc=self.colour, lw=line))
            return 1
        return 0


#Possible TODO: Drawing options for geodesic line segment between two points, other geometry. 

def rootToPt(rts, sizefun = None, colfun = None, shapefun = None):
    # Process 'None' to defaults so defaults only need to set here, not it higher functions
    if sizefun==None:
        sizefun = rootDisc
    if colfun==None:
        colfun = degCol
    if shapefun==None:
        shapefun = circ
    pts = []
    for rt in rts:
        pts.append(shapefun(rt, sizefun = sizefun, colfun = colfun))
    return pts
    

####################################
# Section 3: Drawing the images
####################################

# draw a list of points with size and colour information on the Upper half plane

def plotPointsH(l, scaling=.06,xlims=(-1,1), ylims=(0,2), line=0, edgeCol=(0,0,0,1)):

    fig, ax = plt.subplots()
    ax.axis('off')
    ax = fig.add_subplot(111, aspect='equal')
    ax.set(xlim=xlims,ylim=ylims)
    ptCount = 0
    for pt in l:
        ptCount = ptCount + pt.drawH(ax, scaling, xlims, ylims, line, edgeCol)
    ax.axis('off')
    print("plotPointsH drew " + str(ptCount) + " objects. ")
    return fig

# draw a list of points with size and colour information on the Euclidean plane

def plotPointsE(l, scaling=.06,xlims=(-1,1), ylims=(0,2), line=0, edgeCol=(0,0,0,1)):

    fig, ax = plt.subplots()
    ax.axis('off')
    ax = fig.add_subplot(111, aspect='equal')
    ax.set(xlim=xlims,ylim=ylims)
    ptCount = 0
    for pt in l:
            ptCount =  ptCount+pt.drawE(ax, scaling, xlims, ylims, line, edgeCol)
    ax.axis('off')
    print("plotPointsE drew " + str(ptCount) + " objects. ")
    return fig
    
# Section 4: Utility functions to make the creation of images easier

def polyFamily(pol, bd, height = False, minimal=False, unitCircle=True, coprime=False, arange=None,brange=None,crange=None,drange=None,):
    d = pol.__code__.co_argcount
    ar = None
    br = None
    cr = None
    dr = None
    if d>0: 
        ar = range(1,bd+1)
    if d>1: 
        br = range(-bd,bd+1)
    if d>2: 
        cr = range(-bd,bd+1)
    if d>3: 
        dr = range(-bd,bd+1)
    if(arange != None): ar = arange
    if(brange != None): br = brange
    if(crange != None): cr = crange
    if(drange != None): dr = drange
    pts = polyRange(pol, arange = ar, brange = br, crange = cr, drange = dr, coprime = coprime)
    return rootData(pts, height = height, minimal = minimal, coprime = coprime,unitCircle = unitCircle)
    
def rootPicture(pts, 
                colfun=None, sizefun=None, shapefun=None,
                scaling=.06, xlims=(-1,1), ylims=(0,2)):
    points = rootToPt(pts, colfun=colfun, sizefun=sizefun)
    return plotPointsH(points, scaling=scaling, xlims=xlims, ylims=ylims)

def savePDF(fig, name, path = "StarscapeImages/"):
    fig.savefig(path+name+".pdf", bbox_inches = 'tight', pad_inches = 0)
