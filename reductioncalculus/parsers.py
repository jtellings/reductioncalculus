import re
from classes import *

#===============================================================================
# 1. Type parsers
#===============================================================================

def type_to_list(spec): #adapted from http://andreinc.net/2010/10/05/converting-infix-to-rpn-shunting-yard-algorithm/
    out = []
    stack = []
    specr = spec.replace('E','(s>e)').replace('T','(s>t)')
    
    for i in specr:
        if i in '>(':
            stack.append(i)
        elif i == ')':
            while len(stack) != 0 and stack[-1] != '(':
                out.append(stack.pop())
            stack.pop() 
        elif i in 'set':
            out.append(i)
        else:
            if not i == ' ':
                raise Error('Invalid symbol in type specification: ' + i)
    while len(stack) != 0:
        out.append(stack.pop())
    return out 

# interpret Right Polish type list
def pol_type(L):
    stack=[]
    for x in L:
        if x == '>':
            stack.append(Type(stack.pop(-2),stack.pop()))
        else:
            stack.append(x)
    out = stack.pop()
    if isinstance(out,str):
        return Type(out)        
    else:
        return out

def parse_type(s):
    return pol_type(type_to_list(s))

#===============================================================================
# 2. Syntax parsers
#===============================================================================

#
# The syntax parser consists of separate parsers for different constructs (for lambda terms, 
# where constructs, that construct, assignments, functions. The big 'parse' function chooses
# one of these parsers. All the small parsers in turn recursively call the big parser.
#
#
#

def find_matching_bracket(s,pos,type='('):
    if type=='(':
        ob = '('
        cb = ')'
    elif type=='{':
        ob='{'
        cb='}'
    try:
        if s[pos]==ob:
            i = pos+1
            num = 1
            while num != 0 :
                if s[i] == ob:
                    num += 1
                elif s[i] == cb:
                    num -= 1
                i += 1
            out = i-1
        elif s[pos]==cb:
            i = pos -1
            num = 1
            while num != 0:
                if s[i] == ob:
                    num -= 1
                elif s[i] == cb:
                    num += 1
                i -= 1
            out = i+1
        else:
            raise Error('Position is not a bracket.')
    except IndexError:
        raise Error('Syntax error.')                    
    return out

# parse an assignment of the form 'Xn = ....'
def parse_assign(s):
    t = s.strip()
    if re.match('[A-Z][0-9]* *?=',t):
        p = t.find('=')
        var = s[0:p].strip()
        rest = parse(t[p+1:].strip())
        #return [Keyword('assign'),[var,rest]]
        return Func(Keyword('assign'),[var,rest])
    else:
        raise Error('Not an assignment: '+ t )

def check_assign(s):
    t = s.strip()
    if re.match('[A-Z][0-9]* *?=',t):
        return True
    else:
        return False

# lambda x0 y0 z0 func
# this function returns a match object if it is a valid lambda expression, and false otherwise
def check_lambda(s):
    t = s.strip()
    w = re.match('lambda +([a-z][0-9]* +)*[a-z][0-9]* +',t)
    if w:
        return w
    else:
        return False

# parse a lambda term    
def parse_lambda(s):
    t = s.strip() # remove spaces
    r = check_lambda(t) # check if it is a lambda expression
    if not r:
        raise Error('Syntax error')
    end = r.end() # find the last position in the match object (= last variable in list) 
    if end == len(t): # the last variable is in fact the argument
        end = t.rfind(' ') 
        vars = t[6:sp] # split of last variable
    else:
        vars = t[6:end].strip()
    
    string=''
    stack=[]
    for i,c in enumerate(vars):
        if re.match('[a-z0-9]',c):
            string += c
        elif c==' ':
            stack.append(string)
            string=''
    stack.append(string) # last variable
    rec = parse(t[end:])
    
    rev = stack[::-1] # reverse variable list
    out = Func(Keyword('lambda'),[rev[0],rec])
    for i in rev[1:]:
        out = Func(Keyword('lambda'),[i,out]) # nest multiple lambdas in reverse order
    return out

def check_where(s):
    l = len(s)
    if s[-1] == '}':
        try:
            p=find_matching_bracket(s,l-1,'{')
        except Error:
            return False
        if p>=6:
            #return (s[p-6:p]=='where ')
            return bool(re.fullmatch('.* where *',s[:p])) 
        else:
            return False
    else:
        return False

#parse a where-construct
def parse_where(s):
    t = s.strip()
    l = len(t)
    if not check_where(t):
        raise Error('Syntax error')
    p = find_matching_bracket(t,l-1,'{')
    beg = [m.start() for m in re.finditer('where *',t[0:p])][-1]
    body = t[0:beg].strip()
    stack= []
    pstack=[]
    cstack=[]
    i=p+1
    while i < l:
        c = t[i]
        if c == '{':
            pstack.append(i)        
        elif c=='}':
            if len(pstack)==0: #level 0-closer
                if len(cstack)==0: #no commas
                    rem = t[p+1:i]
                    stack.append(parse(rem))
                else:
                    u = cstack[-1]
                    rem = t[u+1:i]
                    stack.append(parse(rem))
            else:
                pstack.pop()
        elif c==',':
            if len(pstack)==0:    #level-0 comma
                cstack.append(i)
                if len(cstack)==1:
                    rem = t[p+1:i]
                    stack.append(parse(rem))
                else:
                    u = cstack[-2]
                    rem = t[u+1:i]
                    stack.append(parse(rem))
        elif c=='(':
            pstack.append(i)
        elif c==')':
            pstack.pop()
        i+=1
    rec = parse(body)
    return Func(Keyword('where'),[rec,stack])



def check_that(s):
	t = s.strip()
	return (t[:5] == 'that ')

# parse that-construct		
def parse_that(s):
    t = s.strip()
    if t[:5] == 'that ':
        body = t[5:].strip()
    return Func(Keyword('that'),[parse(body)])

# remove redundant brackets
# find last bracket pair [ f(a)(b)(c) --> (c) ]
# recursively apply parser to func part
# list comma-separated arguments, and apply parser recursively
def parse_parentheses(s):
    stack=[]
    pstack=[]
    cstack=[]
    l= len(s)
    if re.fullmatch('[A-Za-z0-9_\*]*',s.strip()):
        return s.strip()
    elif s[-1] != ')':
        raise Error('No final bracket: ' + s)
    else:
        p = find_matching_bracket(s,l-1)
        if p==0: # extra brackets
            return parse(s[1:-1]) 
    
    #print(s[0:p])
    i = p+1
    string=''
    while i < l:
        c = s[i]
        if c not in '(),{} ':
            string += c
        elif c=='(':
            pstack.append(i)
        elif c==')':
            if len(pstack)==0: #level 0-closer
                if len(cstack)==0: #no commas
                    rem = s[p+1:i]
                    stack.append(parse(rem))
                else:
                    u = cstack[-1]
                    rem = s[u+1:i]
                    stack.append(parse(rem))
            else:
                pstack.pop()
        elif c==',':
            if len(pstack)==0:    #level-0 comma
                cstack.append(i)
                if len(cstack)==1:
                    rem = s[p+1:i]
                    stack.append(parse(rem))
                else:
                    u = cstack[-2]
                    rem = s[u+1:i]
                    stack.append(parse(rem))
        elif c=='{':
            pstack.append(i)
        elif c=='}':
            pstack.pop()
        elif c ==' ':
            pass
        else:
            raise SyntaxError('Forbidden character: ' + c)
        i+=1
    funcname = parse(s[0:p])
    return Func(funcname,stack)

#the big parse function
def parse(st):
    s = st.strip()
    if re.fullmatch('[A-Za-z0-9_\*]*',s):    #string
        return s
    elif check_that(s):
        return parse_that(s)
    elif check_assign(s):
        return parse_assign(s)
    elif s[-1] == '}': # ends in }
        return parse_where(s)
    elif check_lambda(s):
        return parse_lambda(s)
    elif s[-1] == ')': # ends in )
        return parse_parentheses(s)    
    else:
        raise Error('Syntax error')

