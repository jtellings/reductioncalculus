import re # regular expressions

varstack = set()

def clearstack():
	global varstack
	varstack = set()

typed=True

#===============================================================================
# 1. Classes for types
#===============================================================================

class AType:
	def __init__(self,name):
		if name in 'set':		# atomic types s,e,t
			self.name=name
		else:
			raise Error('Non-valid atomic type.')
	def __repr__(self):
		return self.name
	def __eq__(self, other):
		if isinstance(other, self.__class__):
			return self.__dict__ == other.__dict__
		elif isinstance(other,Type):		# identify AType('x') and Type('x')
			if isinstance(other,NoType):
				return False
			if other.right == None:
				return self.__dict__ == other.left.__dict__
			else: return False
		else:
			return False
	def __hash__(self):
		return hash(self.name)
		
class Type:
	def __init__(self, left=None, right=None):
		if isinstance(left,str):
			self.left = AType(left)
		else:
			self.left = left
		if isinstance(right,str):
			self.right = AType(right)
		else:
			self.right = right
	def __repr__(self):
		args = self.left, self.right
		if args[1]==None:		# unary types are formally t-->None
			return '{0}'.format(*args)
		else:
			return '({0} --> {1})'.format(*args)
	def __eq__(self, other):
		if isinstance(other, self.__class__):
			return self.__dict__ == other.__dict__
		elif isinstance(other,AType):				# identify AType('x') and Type('x')
			u = Type(other.name)
			return self.__dict__ == u.__dict__ 
		else:
			return False
	def __hash__(self):
		return hash((self.left,self.right))

class NoType(Type):
	def __init__(self):
		Type.__init__(self)
	def __repr__(self):
		return 'NoType'
	def __eq__(self,other):
		return full_equality(self,other)
	def __hash__(self):
		return hash('2f091j20912')

n0 = NoType()

#===============================================================================
# 2. Functions for types
#===============================================================================

def nulltype(tp):
	return (tp == n0 or tp.left == n0)

def tleft(tp):
	if tp == n0: 
		return n0
	elif tp.right is None:
		raise Error('Not a functional type: ' + str(tp))
	else:
		return tp.left

def ptypes(term):
	if isinstance(term,Appl):
		return [ptypes(term.func),ptypes(term.arg)]
	elif isinstance(term,Lambda):
		return [ptypes(term.var),ptypes(term.body)]
	elif isinstance(term,Where):
		j = [ptypes(term.body)]
		for i in term.set:
			j.extend(ptypes(i.left))
			j.extend(ptypes(i.right))
		return j
	elif isinstance(term,PVar) or isinstance(term,RVar) or isinstance(term,Const) or isinstance(term,AConst):
		return [term,term.typ]
	elif isinstance(term,That):
		return [ptypes(term.const)] + [ptypes(u) for u in term.terms] + [ptypes(term.that)]

# check if a type is of the form E^n --> T
def ent(t):
	num = 0
	try:
		while t.left == Type('s','e'):	# left is E
			num += 1
			t = t.right
	except AttributeError:
		num = 0
	if t == Type('s','t'):
		out = num
	else:
		out = 0
	return out

# create type E^n --> T
def create_ent(num):
	typ = Type('s','t')
	for i in range(num):
		typ = Type(Type('e','t'),typ)
	return typ

def deftype(t):
	if isinstance(t,NoType):
		return False
	elif isinstance(t,AType):
		return True
	else:
		if isinstance(t,Type):
			return (deftype(t.right) and deftype(t.left)) #recursive call
		
#------------------------------------------------------------------------------ 
# Type ranking
#------------------------------------------------------------------------------ 

# rank two types tp1 and tp2, returns a list of 0s, 1s, -1s
def typerank(tp1,tp2,stack=None):
	if stack is None:
		stack = []
	
	if tp1 == n0:
		stack.append(1)
	elif tp2 == n0:
		stack.append(2)
	elif isinstance(tp1,Type) and isinstance(tp2,Type):
		if tp1.right is None and tp2.right is None: # atypes
			if tp1 == tp2:
				stack.append(0)
			else:
				stack.append(-1)
		else:	
			s1=typerank(tp1.left,tp2.left)
			s2=typerank(tp1.right,tp2.right)
			stack += s1
			stack += s2
	elif isinstance(tp1,AType) and isinstance(tp2,AType):
		if tp1 == tp2:
			stack.append(0)
		else:
			stack.append(-1)
	else:
		stack.append(-1)
	

	return stack

def typeless(t1,t2):
	q = typerank(t1,t2)
	if set(q).issubset({0,1}):
		return 0
	elif set(q).issubset({0,2}):
		return 1
	else:
		return -1
	
# compare all types in a list pairwise, check consistency. return a list of pairs
def cross(l):
	k = len(l)
	stack = []
	for i in range(k):
		for j in range(i+1,k):
			if (l[i] != l[j]):
				w = typerank(l[i],l[j])
			else:
				continue
			if set(w).issubset({0,1}):
				stack.append( [l[i],l[j]] )
			elif set(w).issubset({0,2}):
				stack.append( [l[j],l[i]])
			elif -1 in w:
				raise Error('Non-unifiable set of types.')
	return stack

def highest(l):
	m = list(set(l))
	k = no_cycles(cross(m))
	if not k:
		return m[-1]
	else:
		return k[-1]

def pos(tp,x):
	if tp == n0:
		return n0
	else:
		if x == 0: #left
			return tp.left
		elif x ==1:
			return tp.right

def build(tp,l):
	if isinstance(tp,Type):
		if tp.right is not None:
			l1 = [pos(x,0) for x in l]
			l2 = [pos(x,1) for x in l]
			return Type(build(tp.left,l1),build(tp.right,l2))
		elif tp == n0:
			return highest(l)
		else: #e,s,t
			return tp
	elif isinstance(tp,AType):
		return tp		

def cbuild(l):
	try:
		m = highest(l)
		return build(m,l)
	except Error as e:
		raise Error('Non-unifiable set of types.' + str(l))

#------------------------------------------------------------------------------ 
# Automatic type assignment functions
#------------------------------------------------------------------------------ 

def assign(term,tp):
	if isinstance(term,PVar) or isinstance(term,RVar):
		try:
			q = cbuild({term.typ,tp})
		except Error:
			s = str(term) + ', ' + str(term.typ) + ', ' + str(tp)
			raise Error('Type assignment problem: ' + s)
		term.typ = q
		return term
	elif isinstance(term,Const):
		return term
	elif isinstance(term,Appl):
		k = Appl(assign(term.func,Type(n0,tp)),term.arg)
		return k
	elif isinstance(term,Lambda): #check if assigned type is functional
		if tp.right is None:
			raise Error(str(tp) + ' is not a functional type')
		else:
			k = Lambda(assign(term.var,tp.left),assign(term.body,tp.right))
			return k
	elif isinstance(term,Where): # assign to body:
		return Where(assign(term.body,tp),term.set)
	elif isinstance(term,That):
		if tp == Type('s','t'):
			return term
		else:
			raise Error('Type assignment problem')
	elif isinstance(term,FVar):
                term.typ = tp
                return term


# assign tp to all *free* vars in form
def assign_vars(var,tp,form):
	if isinstance(form,Appl):
		return Appl(assign_vars(var,tp,form.func),assign_vars(var,tp,form.arg))
	elif isinstance(form,Lambda):
		if isinstance(var,PVar):
			if vareq(form.var,var):
				return form
			else: 
				return Lambda(assign_vars(var,tp,form.var),assign_vars(var,tp,form.body))
		else: #RVar
			return Lambda(form.var,assign_vars(var,tp,form.body))
	elif isinstance(form,Const):
		return form
	elif isinstance(form,Where):
		if isinstance(var,PVar):
			tset = set()
			for i in form.set:
				tset.add(Assignment(i.left,assign_vars(var,tp,i.right)))
			return Where(assign_vars(var,tp,form.body),tset)
		else: #RVar
			if varin(var,[i.left for i in form.set]): #bound variable
				return form
			else:
				tset = set()
				for i in form.set:
					tset.add(Assignment(i.left,assign_vars(var,tp,i.right)))
				return Where(assign_vars(var,tp,form.body),tset)
	elif isinstance(form,PVar) or isinstance(form,RVar):
		if vareq(form,var):
			return assign(form,tp)
		else:
			return form
	elif isinstance(form,That):
		lst = []
		for i in form.terms:
			lst.append(assign_vars(var,tp,i))
		return That(form.const,assign_vars(var,tp,form.that),*lst)

#===============================================================================
# 3. Terms
#===============================================================================

def full_equality(A,B):
    if isinstance(A,B.__class__):
        return A.__dict__ == B.__dict__
    else:
        return False

class Term:
	def __init__(self,typ):
		self.typ = typ
	def __repr__(self):
		return str(self.typ)
	def __eq__(self,other):
		return full_equality(self,other)
		
class Appl(Term):
	def __init__(self,func,arg):
		if not isinstance(func,Term):
			raise Error('Invalid function type: ' +str(func))
		Term.__init__(self,n0)
		if typed:
			atp = cbuild({arg.typ,tleft(func.typ)})
			ftp = cbuild({func.typ,Type(arg.typ,n0)})
			
			self.arg = assign(arg,atp)
			self.func = assign(func,ftp)
			k = self.func.typ
			if k == n0:
				self.typ = n0
			else:
				self.typ = self.func.typ.right
		else:
			self.arg = arg
			self.func = func
			self.typ = n0

	def __repr__(self):
		if isinstance(self.func,Where) or isinstance(self.func,Lambda):
			first = '('+str(self.func)+')'
			out = first+'('+str(self.arg)+')'
		elif isinstance(self.func,Appl):
			out = str(self.func)[:-1]+', ' + str(self.arg) + ')'
		else:
			first = str(self.func)
			out = first+'('+str(self.arg)+')'
		
		return out
	def __hash__(self):
		return hash((self.func,self.arg))
	
class Const(Term):
	def __init__(self,name,typ,pronoun=False):
		if not re.fullmatch('[A-Za-z][0-9]*',name) and re.fullmatch('[A-Za-z0-9_\*]*',name):
			Term.__init__(self,typ)
			self.name=name
			self.pronoun=pronoun
		else:
			raise Error('Invalid name for constant: ' + name)
	def __repr__(self):
		return self.name	
	def __hash__(self):
		return hash(self.name)

# collect bound variables in body (free_PV)
# find their types
# check if consistent
# assign types

class Lambda(Term):
	def __init__(self,var,body):
		if isinstance(var,PVar):
			if typed:
				lv = [u.typ for u in free_PVs(body,var)+[var]]
				bt = cbuild(lv)
				Term.__init__(self,n0)
				self.var = assign(var,bt)
				self.body = assign_vars(var,bt,body)
				ty = Type(self.var.typ,self.body.typ)
				self.typ = ty
			else:
				self.var = var
				self.body = body
				self.typ = n0
		else:
			raise Error(str(var)+': not a pure variable. Type =' + str(type(var)))
	def __repr__(self):
		if isinstance(self.body,Lambda):
			out = 'lambda ' + str(self.var)+ str(self.body)[6:]
		else:
			out = 'lambda '+str(self.var)+' ('+str(self.body)+')'
		return out
	def __hash__(self):
		return hash((self.var,self.body))


class Where(Term):
	def __init__(self,body,assigns):
		rassigns = [x for x in assigns if type(x.left) != FVar]
		fassigns = [x for x in assigns if type(x.left) is FVar]
                
		vars = [x.left for x in assigns] #check for duplicates
		if len(set(vars)) != len(vars):
			raise Error('Duplicates in set.')
		
		if typed:
			newset = set()
			newbody = body
			for i in rassigns:
				types = [u.typ for u in free_RVs(newbody,i.left)] + [i.left.typ,i.right.typ]
				for j in rassigns:
					types.extend([u.typ for u in free_RVs(j.right,i.left)])
				
				h = cbuild(types)
	
				# + assign to all i.right's
				for j in rassigns:
					#newright = assign(assign_vars(i.left,h,j.right),h)
					newright = assign_vars(i.left,h,j.right)
					if vareq(j.left,i.left):
						newset.add(Assignment(assign(i.left,h),assign(newright,h)))
					else:
						newset.add(Assignment(j.left,newright))
				newbody = assign_vars(i.left,h,newbody)
					
			Term.__init__(self,n0)
			self.body = newbody
			newset.update(fassigns)
			self.set = newset
		else:
			self.body = body
			self.set = set(assigns)
			self.typ = n0
		self.typ = self.body.typ
	def __repr__(self):
		h = str(self.body)
		if isinstance(self.body,Where) or isinstance(self.body,Lambda):
			#return '('+h + ') where ' + prty(self.set, len(h)+10)
			return '('+h + ') where ' + str(self.set)
		else:			
			#return h + ' where ' + prty(self.set,len(h)+8)
			return h + ' where ' + str(self.set)
	def vars(self):
		return [x.left for x in self.set if type(x.left) is not FVar]
	def __hash__(self):
		return hash((self.body,tuple(self.set)))

class PVar(Term):
	def __init__(self,letter,number=None):
		if re.fullmatch('[a-z]',letter) and (type(number) is int or number is None):
			Term.__init__(self,n0)
			self.letter = letter
			self.number = number
			#global varstack
			varstack.add((self.letter,self.number))
		else:
			raise Error('Invalid variable.')
	def __repr__(self):
		if self.number is None:
			return self.letter
		else:
			return self.letter + str(self.number)
	def __eq__(self,other):
		return False
	def __hash__(self):
		return hash(self.letter + str(self.number))

class RVar(Term):
	def __init__(self,letter,number=None):
		if re.fullmatch('[A-Z]',letter) and (type(number) is int or number is None):
			Term.__init__(self,n0)
			self.letter = letter
			self.number = number
			#global varstack
			varstack.add((self.letter,self.number))
		else:
			raise Error('Invalid variable.')
	def __repr__(self):
		if self.number is None:
			return self.letter
		else:
			return self.letter + str(self.number)
	def __eq__(self,other):
		return False
	def __hash__(self):
		return hash(self.letter + str(self.number))


class FVar(Term):
        def __init__(self,letter):
                self.letter = letter
                self.typ = n0
        def __repr__(self):
                return '$' + self.letter
        def __eq__(self,other):
                return (self.letter == other.letter)
        def __hash__(self):
                return hash('$' + self.letter)

class Fint:
        def __init__(self,term):
                self.term = term
        def __repr__(self):
                return 'fint(' + str(self.term) + ')'
        
class AConst: # NOT a Term!
	def __init__(self,name,typ):
		self.name = name
		self.typ = typ
	def __eq__(self,other):
		if isinstance(other,self.__class__):
			return self.__dict__ == other.__dict__
		else:
			return False
	def __repr__(self):
		return self.name
	def __hash__(self):
		return hash(self.name)

class That(Term):
	def __init__(self,c,A0,*args):
		if not isinstance(c,AConst):
			raise Error('Invalid that-term')
		if not args:
			raise Error('Invalid that-term: zero arguments')
		m = ent(c.typ)
		if m == 0 or len(args) != m:
			raise Error('Invalid that-term: argument mismatch')
		
		if typed:
			newA0 = assign(A0,Type('s','t'))
			newargs = []
			for i in args:
				newargs.append(assign(i,Type('s','e')))
	
			Term.__init__(self,Type('s','t'))
			self.const = c
			self.that = newA0
			self.terms = newargs
		else:
			Term.__init__(self,Type('s','t'))
			self.const = c
			self.that = A0
			self.terms = list(args)
	def __eq__(self,other):
		if isinstance(other,self.__class__):
			return self.__dict__ == other.__dict__
		else:
			return False
	def __repr__(self):
		out = str(self.const) + '(' + str(self.terms[0])
		for i in self.terms[1:]:
			out += ', ' + str(i)
		out += ', that ' + str(self.that) + ')'
		return out
	def __hash__(self):
		return hash((self.const,self.that,tuple(self.terms)))

class Assignment:
	def __init__(self,left,right):
		if isinstance(left,RVar) and isinstance(right,Term):
			self.left = left
			self.right = right
		elif isinstance(left,FVar):
                        self.left = left
                        self.right = right
		else:
                        raise Error('Type mismatch.')
	def __repr__(self):
		return str(self.left) + ' := ' + str(self.right)
	def __eq__(self,other):
		if isinstance(other,self.__class__):
			return self.__dict__ == other.__dict__
		else:
			return False
	def __hash__(self):
		return hash(tuple([self.left,self.right]))

#===============================================================================
# 4. Other functions
#===============================================================================

def vareq(var1,var2):
        if isinstance(var1,FVar) and isinstance(var2,FVar):
                return (var1.letter == var2.letter)
        else:
                return (var1.letter == var2.letter and var1.number == var2.number)

def free_PVs(form,var):
	if isinstance(form,Appl): # union of free vars in function argument
		return free_PVs(form.func,var) + free_PVs(form.arg,var)
	elif isinstance(form,Lambda): # free vars in lambda body
		if vareq(var,form.var):
			return [] #just ignore these bound vars
		else:
			return free_PVs(form.body,var)
	elif isinstance(form,Where):
		temp = free_PVs(form.body,var) # free vars in the where body
		for i in form.set:
			temp.extend(free_PVs(i.right,var)) # free vars in each assignment
		return temp	
	elif isinstance(form,That):
		temp = []
		for i in form.terms:
			temp.extend(free_PVs(i,var))
		return temp + free_PVs(form.that,var)
	elif isinstance(form,PVar):
		if vareq(var,form):
			return [form] # free var
		else:
			return [] # bound var, return empty set
	else: # const or rvar
		return [] # return empty set

def free_RVs(form,var):
	if isinstance(form,Appl): # union of free vars in function argument
		return free_RVs(form.func,var) + free_RVs(form.arg,var)
	elif isinstance(form,Lambda): # free vars in lambda body
		return free_RVs(form.body,var)
	elif isinstance(form,Where):
		if varin(var,[i.left for i in form.set]):
			return [] # ignore these bound vars
		else:
			temp = free_RVs(form.body,var) # free vars in the where body
			for i in form.set:
				temp.extend(free_RVs(i.right,var)) # free vars in each assignment
			return temp	
	elif isinstance(form,That):
		temp = []
		for i in form.terms:
			temp.extend(free_PVs(i,var))
		return temp + free_PVs(form.that,var)
	elif isinstance(form,RVar):
		if vareq(var,form):
			return [form] # free var
		else:
			return [] # bound var, return empty set
	else: # const or pvar
		return [] # return empty set

def varin(v,lst):
	for i in lst:
		if vareq(i,v):
			return True
	return False

def str_to_int(s):
	if s == '':
		return None
	else:
		return int(s)

def isnum(x):
	try:
		int(x)
		return True
	except ValueError:
		return False

#for internal use: keywords such as 'where', 'lambda', 'that'
class Keyword:
    def __init__(self,name):
        self.name = name
    def __repr__(self):
        return self.name
    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.__dict__ == other.__dict__
        else:
            return False
		
# a non-typed function class.
# not part of the official language, only used for internal reasons
class Func:
	def __init__(self, func, args=None):
		self.func=func
		self.args = args
	def print1(self):
		if isinstance(self.func,str):
			t=''.join(map(lambda x: str(x)+', ',self.args[:-1]))
			return self.func +'('+t+str(self.args[-1])+')'
		elif isinstance(self.func,Keyword):
			t=''.join(map(lambda x: str(x)+', ',self.args[:-1]))
			return str(self.func) +'('+t+str(self.args[-1])+')'
		elif isinstance(self.func,Func):
			t=''.join(map(lambda x: str(x)+', ',self.args[:-1]))
			return self.func.print1()+'('+t+str(self.args[-1])+')'
	def __repr__(self):
		return self.print1()

class Error(Exception):
     def __init__(self, value):
         self.value = value
     def __str__(self):
         return repr(self.value)

def no_cycles(graph):
	l = []
	gc = graph[:]
	incoming = [x[0] for x in graph]
	outgoing = [x[1] for x in graph]
	nodes = set(incoming+outgoing) 
	s = [x for x in nodes if x not in outgoing]
	
	while s:
		n = s.pop()
		l.append(n)
		out = [x[1] for x in gc if x[0]==n]
		for z in out:
			gc.remove([n,z])
			if not [x[0] for x in gc if x[1] == z]:
				s.append(z)
	if gc:
		l = False
	return l	

#===============================================================================
# 5. Tests
#===============================================================================

def test():
	x = PVar('x',0)
	y = PVar('y',1)
	x.typ = Type('e',n0)
	a = Appl(x,y)
	b = assign(a,Type('s'))
	return b

def test2():
	lv = Const('loves',Type('e',Type('e','t')))
	x = PVar('x',0)
	y = PVar('y',0)
	a = Appl(Appl(lv,x),y)
	return a



