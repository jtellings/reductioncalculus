
import re	# regular expressions
import itertools # i use some of these to check for permutations



import classes as c	# Class definitions
import parsers as p		# Type and syntax parsers


names = dict() # global dictionary of names and types
pronouns = ['he','she','him','her']
lfs = []	# global list of LFs

def myjoin(s1,s2):
	if '\n' in s2:
		pass
	else:
		return s1 + s2

#===============================================================================
# 1. Object management
#===============================================================================

# add an object on the basis of a type specification 'name : type a/d'
def add_object(str,overwrite=True):

	s = str.strip()		# remove extra spaces
	att = False			# default denotational
	out = s
	if s[-1] == 'a':
		att = True
		out = s[:-1].strip() # remove 'a' part
	elif s[-1] == 'd':
		att = False
		out = s[:-1].strip() # remove 'd' part
	r = out.split(':')	# split by semicolon
	name = r[0].strip() # the first part is the name
	tp = p.parse_type(r[1].strip()) # the second part is the type
	
	global names
	
	if name in names: # existing object
		if not overwrite:
			raise c.Error(name + ' already exists.')

	if re.fullmatch('[a-z][0-9]*',name):
		raise c.Error('Can\'t introduce variable ' + name)
		#names.update({ name : c.PVar(name,tp)}) # pure variable
	elif re.fullmatch('[A-Z][0-9]*',name):
		raise c.Error('Can\'t introduce variable ' + name)
		#names.update({ name : c.RVar(name,tp)}) # recursive variable
	else:
		if ' ' in name: 
			raise c.Error(name + ' not a valid name.') # contains space
		else:
			if att:
				names.update({ name : c.AConst(name,tp)})
			else:
				names.update({ name : c.Const(name,tp)}) # constant

def remove_object(name):
	global names
	
	try:
		names.pop(name)
	except KeyError:
		raise c.Error('No object ' + name)	

def remove_objects(l):
	for i in l:
		remove_object(i)

def add_objects(l):
	for i in l:
		add_object(i)

# Read a file with object specifications. The default file name is 'inputfile'.
def readfile(url='inputfile'):
	try:
		f = open(url, 'r')
	except FileNotFoundError:
		raise c.Error('No such file: ' + url)
		
	content = [line.rstrip().split('#',1)[0] for line in f] # read each line, remove spaces, split by # sign
	f.close()

	types=[] #initialize list for type lines
	global names
	global lfs

	for line in content:	#sort type specifications and LFs
		if line[0:5] == 'echo ' or line[0:1] == '@':
			apply_settings(line)
			lfs.append(line)
			continue
		elif ':' in line:
			types.append(line.replace(' ',''))
		elif not line.lstrip()=='':		#ignore empty lines
			lfs.append(line)
	for i in types:
		add_object(i,True)

def apply_settings(line):
        global pronouns
        if line[1:9] == 'pronouns':
                lst = [x.strip() for x in line[9:].split(',')]
                pronouns = lst
                
#===============================================================================
# 2. Additional parse functions
#===============================================================================

# if last argument is that function:

def func_to_term(f):
	global names
	global pronouns
	if isinstance(f,str): # string
		if re.fullmatch('[a-z][0-9]*',f):
			n = (None if f[1:]=='' else int(f[1:]))
			return c.PVar(f[0],n)
		elif re.fullmatch('[A-Z][0-9]*',f):
			n = (None if f[1:]=='' else int(f[1:]))
			return c.RVar(f[0],n)
		elif f in pronouns:
			return c.Const(f,c.Type('s','e'),True)
		else:
			try:
				out = names[f]
				if isinstance(out,c.Term):
					return out
				else:
					raise c.Error('Not a term: ' + f)
			except KeyError:
				raise c.Error('No such object: ' + f)
	m = f.func # function part
	a = f.args # argument part
	
	j = [(isinstance(x,c.Func) and x.func == c.Keyword('that')) for x in a]
	if any(j[:-1]):
		raise c.Error('Non-final that')
	else:
		if j[-1]: # that-clause
			try:
				return c.That(names[m],func_to_term(a[-1].args[0]),*[func_to_term(x) for x in a[:-1]])
			except KeyError:
				raise c.Error('No such attitudinal constant: ' + str(m))
	if isinstance(m,str) or isinstance(m,c.Func):
		try:
			out = func_to_term(m) # recursive call on function part
			for i in a:
				out = c.Appl(out,func_to_term(i)) # recursive call on each argument
			result = out
		except KeyError:
			raise c.Error('No such object: ' + str(m))
	elif m == c.Keyword('lambda'):
		try:
			result = c.Lambda(func_to_term(a[0]),func_to_term(a[1])) # recursive call for lambda term
		except KeyError:
			raise c.Error('No such object: ' + str(a[0]))
	elif m == c.Keyword('where'):
		result = c.Where(func_to_term(a[0]),{ func_to_term(i) for i in a[1] }) # recursive call for wh construct
	elif m == c.Keyword('assign'):
		result = c.Assignment(func_to_term(a[0]),func_to_term(a[1])) # recursive call for assignments
	else:
		pass
	return result						


def fullparse(str):
	return func_to_term(p.parse(str))

#===============================================================================
#  3. Variable renaming
#===============================================================================

fixedletter = 'Aa'

def newvar(letter,typ,fixed=False):
	if letter.isupper():
		l = fixedletter[0] if fixed else letter
	else:
		l = fixedletter[1] if fixed else letter
		
	if l in [i[0] for i in c.varstack]: #letter present
		nums = [i[1] for i in c.varstack if i[0] == l]
		if nums == [None]:
			new = 0
		elif [x for x in nums if x is not None]:
			new = max([x for x in nums if x is not None])+1
		if l.islower(): # PVAR
			return c.assign(c.PVar(l,new),typ)
		else:
			return c.assign(c.RVar(l,new),typ)
	else: #letter not present
		if l.islower():
			return c.assign(c.PVar(l,None),typ)
		else:
			return c.assign(c.RVar(l,None),typ)


def newfvar(letter):
        if '$'+letter not in c.varstack:
                c.varstack.add('$'+letter)
                return c.FVar(letter)
        else:
                out = []
                for i in [x for x in c.varstack if isinstance(x,str)]:
                        if re.fullmatch('\$'+letter+'[0-9]*',i):
                                out.append( int('0'+i[2:]) )
                m = max(out)+1
                c.varstack.add('$'+letter+str(m))
                return c.FVar(letter+str(m))
        
def rename(term,stack=None):
	if stack is None:
		stack = dict()
	
	if isinstance(term,c.PVar) or isinstance(term,c.RVar):
		if str(term) in stack:
			s = stack[str(term)]
			out = s
		else:
			s = str(term)
			nv = newvar(s[0],term.typ)
			stack.update({ s : nv })
			out = nv
	elif isinstance(term,c.Lambda):
		s = str(term.var)
		old = []
		if s in stack:
			old = [s,stack.pop(s)] # store old one
		
		nv = newvar(s[0],term.var.typ)
		stack.update({ s : nv})
		out1 = rename(term.body,stack)
		stack.pop(s)
		if old:
			stack.update({old[0] : old[1]}) #restore old one
		out = c.Lambda(nv,out1)
	elif isinstance(term,c.Appl):
		out = c.Appl(rename(term.func,stack),rename(term.arg,stack))
	elif isinstance(term,c.Const) or isinstance(term,c.FVar):
		out = term
	elif isinstance(term,c.Fint):
                out = c.Fint(rename(term.term,stack))
	elif isinstance(term,c.Where):
		old = []
		vars = term.vars()
		for i in vars: # store old stack
			s = str(i)
			if s in stack: #already a free var
				old.append([s,stack.pop(s)])
		
		for i in vars: # update stack with new bound vars
			nv = newvar(i.letter,i.typ)
			stack.update({ str(i) : nv})
		
		out2 = rename(term.body,stack) #recursive call on body
		st = set()
		for i in {x for x in term.set }: #recursive call on set
			st.add(c.Assignment(rename(i.left,stack),rename(i.right,stack)))
		
		for i in vars: #remove bound vars
			stack.pop(str(i))
		
		for i in old: #restore old stack
			stack.update({ i[0] : i[1] })
		
		out = c.Where(out2,st)
	elif isinstance(term,c.That):
		lst = [rename(x,stack) for x in term.terms]
		out = c.That(term.const,rename(term.that,stack),*lst)
	
	return out

#===============================================================================
# 4. Immediacy
#===============================================================================


# check if a term is of the form p(v1,....vn) with p recursive, and v_i pure
def rec_appl(term):
	if not isinstance(term,c.Appl):
		return False
	while isinstance(term,c.Appl):
		if not isinstance(term.arg,c.PVar):
			return False
		term = term.func
			
	return isinstance(term,c.RVar)

def immediate(term):
	if isinstance(term,c.PVar) or isinstance(term,c.RVar):
		return True
	elif isinstance(term,c.Lambda):
		out = term
		while isinstance(out,c.Lambda):
			out = out.body
		return (isinstance(out,c.RVar) or rec_appl(out))
	elif isinstance(term,c.Appl):
		return rec_appl(term)
	else:
		return False

#===============================================================================
# 5. Reduction rules
#===============================================================================

# --- Some auxiliary functions

# replace([[P1,x],...], form)
def replace_free_RVs(reps,form,bound=None):
	if bound is None:
		bound = []
		
	if isinstance(form,c.Appl):
		return c.Appl(replace_free_RVs(reps,form.func),replace_free_RVs(reps,form.arg,bound))
	elif isinstance(form,c.Lambda): # free vars in lambda body
		return c.Lambda(form.var,replace_free_RVs(reps,form.body,bound))
	elif isinstance(form,c.Where):
		vs = form.vars()
		bound.extend(vs)
		
		newbody = replace_free_RVs(reps,form.body,bound) # free vars in the where body
		temp = set()
		for i in form.set:
			temp.add(c.Assignment(i.left,replace_free_RVs(reps,i.right,bound))) # free vars in each assignment
		bound = [x for x in bound if x not in vs]
		return c.Where(newbody,temp)	
	elif isinstance(form,c.That):
		temp = []
		for i in form.terms:
			temp.append(replace_free_RVs(reps,i,bound))
		return c.That(form.const,form.that,*temp)
	elif isinstance(form,c.RVar):
		if c.varin(form,[x[0] for x in reps]):
			if not c.varin(form,bound):
				r = [x[1] for x in reps if c.vareq(x[0],form)][0]
				return r
			else: #bound var
				return form
		else:
			return form
	else: # const or pvar
		return form

def termeq(t1,t2):
	if isinstance(t1,c.Appl) and isinstance(t2,c.Appl):
		return termeq(t1.func,t2.func) and termeq(t1.arg,t2.arg)
	
	elif isinstance(t1,c.PVar) and isinstance(t2,c.PVar):
		return c.vareq(t1,t2)
	elif isinstance(t1,c.RVar) and isinstance(t2,c.RVar):
		return c.vareq(t1,t2)
	elif isinstance(t1,c.Assignment) and isinstance(t2,c.Assignment):
                return (c.vareq(t1.left,t2.left) and termeq(t1.right,t2.right))
	elif isinstance(t1,c.Const) and isinstance(t2,c.Const):
		return (t1 == t2)
	elif isinstance(t1,c.Lambda) and isinstance(t2,c.Lambda):
		return (c.vareq(t1.var,t2.var) and termeq(t1.body,t2.body))
	elif isinstance(t1,c.Where) and isinstance(t2,c.Where):
		bl = termeq(t1.body,t2.body)
		lst = [] 
		for i in t1.set:
			uniq = [x for x in t2.set if c.vareq(x.left,i.left)]
			if len(uniq) == 1:
				uniq2 = uniq[0].right
			else:
				return False
			ye = termeq(i.right,uniq2)
			lst.append(ye)
		return bl and all(lst)
	elif isinstance(t1,c.That) and isinstance(t2,c.That):
		beg = (t1.const == t2.const) and termeq(t1.that,t2.that)
		if not len(t1.terms) == len(t2.terms):
			return False
		lst = []
		for i,s in enumerate(t1.terms):
			lst.append( termeq(s,t2.terms[i]) )
		return beg and all(lst)
	else:
		return False

# --- The reductions themselves

def reduce_hr(t): # Head Rule
	
	if isinstance(t,c.Where) and isinstance(t.body,c.Where):
		k = t.set.union(t.body.set) # take the union of the two sets
		r = c.Where(t.body.body,k)
		return r
	else: # not the right form for this rule
		return t
	
def reduce_bs(t):

	if isinstance(t,c.Where):
		newset = set()
		for i in t.set:
			if isinstance(i.right,c.Where):
				newset.add(c.Assignment(i.left,i.right.body))
				newset.update(i.right.set)
			else:
				newset.add(i)
		#print(newset)
		return c.Where(t.body,newset)
	else:
		return t 

def reduce_recap(t):

	if isinstance(t,c.Appl) and isinstance(t.func,c.Where):
		out = c.Where(c.Appl(t.func.body,t.arg),t.func.set)
		return out
	else:
		return t

def reduce_ap(t):

	if isinstance(t,c.Appl) and not immediate(t.arg):
		nv = newvar('P',c.n0)
		out = c.Where(c.Appl(t.func,nv),{c.Assignment(nv,t.arg)})
		return out
	else:
		return t

def reduce_l(t):
		
	if isinstance(t,c.Lambda) and isinstance(t.body,c.Where):
		
		replacements = [[x,c.Appl(newvar(x.letter,c.n0),t.var)] for x in t.body.vars()]
		#print(replacements)
		
		newbody = replace_free_RVs(replacements,t.body.body)
		newset = set()
		
		for i in t.body.set:
			var = [x for x in replacements if c.vareq(x[0],i.left)][0] # [P1, P2(u)]
			new = c.Assignment(var[1].func,c.Lambda(t.var,replace_free_RVs(replacements,i.right)))
			newset.add(new)

		return c.Where(c.Lambda(t.var,newbody),newset)
	else:
		return t

# --- Rules for 'that'


#this function works on a CF, creates fresh PVars for each RVar, and keeps a list of variable renamings	
def fint_repl(t,stack=None,bound=None):
	
	if stack is None:
		stack = []
	if bound is None:
                bound = []
	
	if isinstance(t,c.Appl): 
		out = c.Appl(fint_repl(t.func,stack,bound)[0],fint_repl(t.arg,stack,bound)[0])
	elif isinstance(t,c.Lambda):
		bound.append(t.var)
		out = c.Lambda(t.var,fint_repl(t.body,stack,bound)[0])
		
	elif isinstance(t,c.Const):
		out = t
	elif isinstance(t,c.Where):
		bound.extend(t.vars())
		newbody = fint_repl(t.body,stack,bound)[0]
		newset = set()
		for i in t.set:
			newset.add(c.Assignment(i.left,fint_repl(i.right,stack,bound)[0]))
		out = c.Where(newbody,newset)
	elif isinstance(t,c.RVar):
		if c.varin(t,[x[0] for x in stack]):
			out = [x[1] for x in stack if c.vareq(x[0],t)][0]
		else:
			nv = newvar(t.letter.lower(),t.typ) #create new PVar
			stack.append([t,nv])
			out = nv
	elif isinstance(t,c.PVar):
		stack.append([t,t])
		out = t
	elif isinstance(t,c.That):
		newlst=[]
		for i in t.terms:
			newlst.append(fint_repl(i,stack,bound)[0])
		out = c.That(t.const,fint_repl(t.that,stack,bound)[0],*newlst)
	
	free_vars = [x for x in stack if not c.varin(x[0],bound)]
	stack2 = [x for x in stack if c.varin(x[0],bound) and isinstance(x[0],c.RVar)]
	return [out,stack2,free_vars]


def cf(t):
	j = recreduce(t)
#	while isinstance(j,Reduce):
#		j = j.b[0]
	
	return j

def fint(t):
	allsteps = cf(t)
	cfm = allsteps
	while isinstance(cfm,Reduce):
		cfm = cfm.b[0] #get to Canonical Form
	#cfm = cf(t) # no renaming
	
	fi = fint_repl(cfm)
	
	fi0 = fi[0]
	
	if not isinstance(fi0,c.Where):
		fi0 = c.Where(fi0,set()) 	# A = A where {}
	
	vars = [x[1] for x in fi[1]] + [x[1] for x in fi[2]] # variables to be abstracted over
	
	def lmb(x,st): #construct a lambda term with all variables in st
		out = x
		for i in st:
			if isinstance(i,c.RVar):
				v = newvar(i.letter.lower(),i.typ)
			else:
				v = i
			out = c.Lambda(v,out)
		return out
	
	lst = [[x[0] for x in fi[2]],[lmb(fi0.body,vars)]] # all free variables, and the body
	for i in fi0.set: #now add all the terms in the where-construct
		lst[1].append(lmb(i.right,vars))
	return lst+[allsteps] #return the whole list and reduction steps

starred = set()	#this stores which names (knows*, knows**, knows*** etc.) have been used
def star(t):
	global starred
	out = t+'*'
	while out in starred or out in names:
		out = out + '*'
	
	starred.add(out)
	return out

def reduce_that(t):
	if isinstance(t,c.That):
		fi = fint(t.that)
		k = len(fi[0])+len(fi[1])
		typ = c.create_ent(k)
		newname = star(str(t.const))
		newcons = c.Const(newname,c.n0)

		allargs = t.terms + fi[0] + fi[1]
		out = c.Appl(newcons,allargs[0])
		for i in allargs[1:]:
			out = c.Appl(out,i)
		return [out,fi[2]]
	else:
		return t

# ---- Reduce class
# f = [fvar1, X]
def repl_fvars(f,trm):
        fin = fint(f[1])
        lm = fin[2]
        vars = [newvar('P',c.n0) for x in range(len(fin[1]))]
        def recur(t,fi):
                if isinstance(t,c.That):
                        if isinstance(t.that, c.FVar):
                                # special
                                #rp = [x[1] for x in f if x[0] == t.that][0]
                                if t.that == f[0]:
                                        newname = star(str(t.const))
                                        newcons = c.Const(newname,c.n0)

                                        allargs = t.terms + fi[0] + vars
                                        out = c.Appl(newcons, allargs[0])
                                        for i in allargs[1:]:
                                                out = c.Appl(out,i)
                                        return out
                        else:
                                return t
                elif isinstance(t,c.Const) or isinstance(t,c.RVar) or isinstance(t,c.PVar):
                        return t
                elif isinstance(t,c.Appl):
                        return c.Appl(recur(t.func,fi), recur(t.arg,fi))
                elif isinstance(t,c.Lambda):
                        return c.Lambda(c.var, recur(t.body,fi))
                elif isinstance(t,c.Where):
                        lst = [ c.Assignment(i.left,recur(i.right,fi)) for i in t.set ]
                        return c.Where(recur(t.body,fi),lst)
                else:
                        return t

        final = [ c.Assignment(vars[i], fin[1][i]) for i in range(len(vars)) ]
        n = recur(trm,fin)
        removal = set([x for x in n.set if x.left == f[0]])
        newset = n.set.difference(removal)
        if newset == set():
                n = n.body
        else:
                n.set = newset
        where = c.Where(n, final)

        return [where,lm]


def reduce_intens(t):
        if isinstance(t,c.Where) and any([type(x.left) is c.FVar for x in t.set]):
                rl = [[x.left,x.right.term] for x in t.set if type(x.left) is c.FVar][0]
                u = repl_fvars(rl,t)
                return u
               # removal = set([x for x in t.set if type(x.left) is c.FVar])
               # newset = t.set.difference(removal)
                # if newset == set():
                #         u = repl_fvars(rl,t.body)[0]
                #         return u
                # else:                        
                #         t.set = newset
                #         u = repl_fvars(rl,t)[1]
                #         return u
        else:
                return t

class Reduce():
    def __init__(self,form,branches,label):
        self.f = form
        self.b = branches
        self.l = label
        self.lem = None
    def __repr__(self):
        return '(' + str(self.f) + ', ' +str(self.b) +', '+ str(self.l) + ')'

def help(s):
	if isinstance(s,Reduce):
		return s.b[0]
	else:
		return s

def reduceR(r,ren=True):
    if isinstance(r,Reduce):
    	t = r.b[0]
    	return reduceR(t)
    else:
    	t = r
    if isinstance(t,c.Where) and any([type(x.left) is c.FVar for x in t.set]):
            ri = reduce_intens(t)
            p = Reduce(t,[ri[0]],'(intensional)')
            p.lem = ri[1]
            return p
    elif isinstance(t,c.Where) and isinstance(t.body,c.Where):
        return Reduce(t,[reduce_hr(t)],'(hr)')
    elif isinstance(t,c.That):
    	rd = reduce_that(t)
    	p = Reduce(t,[rd[0]],'(that)')
    	p.lem = rd[1]
    	return p
    elif isinstance(t,c.Lambda) and isinstance(t.body,c.Where):
        return Reduce(t,[reduce_l(t)],'(lambda)')
    elif isinstance(t,c.Where) and any([isinstance(i.right,c.Where) for i in t.set]):
        return Reduce(t,[reduce_bs(t)],'(BS)')
    elif isinstance(t,c.Appl) and isinstance(t.func,c.Where):
        return Reduce(t,[reduce_recap(t)],'(recap)')
    elif isinstance(t,c.Appl) and not immediate(t.arg):
    	return Reduce(t,[reduce_ap(t)],'(ap)')
    elif isinstance(t,c.Appl):
        ff = reduceR(t.func)
        aa = reduceR(t.arg)
        out = c.Appl(help(ff),help(aa))
        s = rmv([ff,aa])
        if s:
        	return Reduce(t,[out]+s,'(rep1)')
        else:
        	return t
    elif isinstance(t,c.Lambda):
        bdy = reduceR(t.body)
        return Reduce(t,[c.Lambda(t.var,help(bdy)),bdy],'(rep2)')
    elif isinstance(t,c.Where):
        bdy = reduceR(t.body)
        lst = [bdy]
        nset = set()
        for i in t.set:
            r = reduceR(i.right)
            lst.append(r)
            nset.add(c.Assignment(i.left,help(r)))
        out = c.Where(help(bdy),nset)
        s = rmv(lst)
        if s:
        	return Reduce(t,[out]+s,'(rep3)')
        else:
        	return out
    else:
        #return Reduce(t,[t],'')
        return t

def rmv(l):
	out = [x for x in l if isinstance(x,Reduce)]
	return out

def termR(t1,t2):
    if isinstance(t1,Reduce):
        k = t1.f
    else:
        k = t1
    if isinstance(t2,Reduce):
        m = t2.f
    else:
        m = t2
    
    if isinstance(k,c.Term) and isinstance(m,c.Term):
        return termeq(k,m)
    else:
        return termR(k,m)
    	
def recreduce(t):
	k = reduceR(t)
	if not isinstance(k,Reduce):
		return k
	if not termR(k,k.b[0]):
		k.b[0] = recreduce(k)
		return k
	else:
		return k
    
def all_labels(r):
    if not isinstance(r,Reduce):
        return []
    stack = [r.l]
    for i in r.b:
        if isinstance(i,Reduce):
            for j in all_labels(i):
                stack.append(j)
    return stack

#list of pairs [form, [labels]]

class PrintObj():
	def __init__(self,form,lemmata=None):
                if lemmata is None:
                        lemmata = []
                self.form = form
                self.lem = lemmata
	def __hash__(self):
		return hash((self.form,self.lem))

def printlist(s,lemmata=None):
    #pr = s
    if not isinstance(s,PrintObj):
    	s = PrintObj(s,lemmata)
    
    out = []	
    stack = []
    if lemmata is None:
    	lemmata = []
    r = s.form
    if isinstance(r,Reduce):
    	if len(r.b) > 1:
    		for x in r.b[1:]:
    			stack += all_labels(x)
    			stack = [x for x in stack if x not in ['(rep1)','(rep2)','(rep3)'] ]
    			if isinstance(x.lem,Reduce):
                                lemmata += [printlist(x.lem,lemmata)]
                                stack += ['Lemma']


    	out.append([r.f])
    	#print(lemmata)
    	
    	if r.l in ['(rep1)','(rep2)','(rep3)']:
    		if stack:
    			out[-1].append(stack)
    			out += printlist(r.b[0],lemmata).form
    	else:
    		out[-1].append([r.l])
    		if r.lem:
    			out[-1][-1].append('Lemma')
    			#lemmata.append( printlist(r.lem[0]).form )
    			lemmata.insert(0, printlist(r.lem,lemmata))
    			#print('add ' + str(lemmata))

    		out += printlist(r.b[0],lemmata).form
    else:
    	out.append([r,'0'])

    #print('end: ' + str(lemmata) )#+ '   o: ' + str(out))
    if len(out[-1])==1:
    	out[-1].append('0')


    return PrintObj(out,lemmata)
    
        
#readfile()
#k = fullparse('every(man)(lambda u danced(u,wife(u)))')

#fullparse('knows(John, that woman(Mary))')
#wow = f3f319j(k)

#readfile()
#readfile('SETTINGS')
#ccc = fullparse('dummy(knows(John, that flat(earth)))')
#ro = recreduce(ccc)


#===============================================================================
#  Tests
#===============================================================================

def test_reduce():
	add_objects(['Paul : E','John : E', 'wife : E >E', 'loves : E>E>T'])
	ex1 = fullparse('(loves(J,W) where {W = wife(P), P = Paul}) where {J = John}')
	return fullreduce(ex1) 

def test_immediate():
	add_object('John : E')
	
	# desired output: T, T, T, F, F, F, T, F, T, F, F
	print(immediate(fullparse('x2')) is True)
	print(immediate(fullparse('Q1')) is True)
	print(immediate(fullparse('Q1(x1,x2,x3,x4)')) is True)
	print(immediate(fullparse('q1(x1,x2,x3,x4)')) is False)
	print(immediate(fullparse('q1(x1,x2,John,x4)')) is False)
	print(immediate(fullparse('Q1(x1,x2,John,x4)')) is False)
	print(immediate(fullparse('lambda x1 x2 x3 (Q1)')) is True)
	print(immediate(fullparse('lambda x1 x2 x3 (John)')) is False)
	print(immediate(fullparse('lambda x1 x2 x3 (Q1(x4,x3,x2,x1))')) is True)
	print(immediate(fullparse('lambda x1 x2 x3 (Q1(x4,John,x2,x1))')) is False)
	print(immediate(fullparse('lambda x1 x2 x3 (q1(x4,x3,x2,x1))')) is False)
	
	remove_objects(['John'])

def parsertest():
	lf1 = 'every(man)(lambda u (danced(u,wife(u))))'
	add_object('every : (E > T) > ((E>T)>T)')
	add_object('man : E>T')
	add_object('danced : E > E > T')
	add_object('wife : E > E')
	a1 = fullparse(lf1)
	print('input: \'' + lf1 + '\'')
	print('output: ' + str(a1) + ' of type ' + str(a1.typ))
	lf2 = '(lambda x (loves(x,x)))(J) where {J = John}'
	add_object('loves : E > E > T')
	add_object('John : E')
	a2 = fullparse(lf2)
	print('input: \'' + lf2 + '\'')
	print('output: ' + str(a2) + ' of type ' + str(a2.typ))
	remove_objects(['every','man','danced','wife','loves','John'])


def testf():
        readfile('SETTINGS')
        j = names['John']
        tst = c.Assignment(c.FVar('w'),2)
        reg = c.Assignment(c.RVar('X',4),j)

        return [j,tst,reg]

def testRPL():
        readfile('SETTINGS')
        readfile()
        j = c.That(names['knows'],c.FVar('w'),names['John'])
        j2 = c.Where(j,[c.Assignment(c.FVar('w'),c.Fint(fullparse('flat(earth)')))])
        d = [[c.FVar('w'), fullparse('flat(earth)')]]
        return j2


## to fix:

## lambda x (XXX that $p) doesn't print well
## extend newvar to $p
