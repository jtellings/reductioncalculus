import sys
import main
import argparse
import os.path

parser = argparse.ArgumentParser()
parser.add_argument("filename", help="the input file")
parser.add_argument("-v","--verbose",type=int, choices=[0,1,2], help="specify verbosity level (default=0)")
parser.add_argument("-p","--pause",help="pause at each reduction step (default=True)", action="store_true")
parser.add_argument("-o","--output",help="output to file")
args = parser.parse_args()

output_to_file = args.output

vrb = args.verbose
if vrb is None: vrb = 0

pause = args.pause

maxlen = 80 # default value

class _Getch:
    """Gets a single character from standard input. Does not echo to the
    screen."""
    def __init__(self):
        try:
            self.impl = _GetchWindows()
        except ImportError:
            try:
                self.impl = _GetchUnix()
            except ImportError:
                self.impl = _GetchMacCarbon()
 
    def __call__(self):
        # Return as a string
        char = self.impl()
        if char == '\x03':
            raise KeyboardInterrupt
        elif char == '\x04':
            raise EOFError
        return char
        #return self.impl().decode('utf-8')
 
     
class _GetchUnix:
    def __init__(self):
        import tty, sys
 
    def __call__(self):
        import sys, tty, termios
        fd = sys.stdin.fileno()
        old_settings = termios.tcgetattr(fd)
        try:
            tty.setraw(sys.stdin.fileno())
            ch = sys.stdin.read(1)
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)
        return ch
 
 
class _GetchWindows:
    def __init__(self):
        import msvcrt
 
    def __call__(self):
        import msvcrt
        return msvcrt.getch()
 
 
class _GetchMacCarbon:
    """
    A function which returns the current ASCII key that is down;
    if no ASCII key is down, the null string is returned. The
    page http://www.mactech.com/macintosh-c/chap02-1.html was
    very helpful in figuring out how to do this.
    """
    def __init__(self):
        import Carbon
        Carbon.Evt #see if it has this (in Unix, it doesn't)
 
    def __call__(self):
        import Carbon
        if Carbon.Evt.EventAvail(0x0008)[0]==0: # 0x0008 is the keyDownMask
            return ''
        else:
            (what,msg,when,where,mod)=Carbon.Evt.GetNextEvent(0x0008)[1]
            return chr(msg & 0x000000FF) 

#resolve pronouns
def resolve(term):
    out = []        
    if isinstance(term,main.c.PVar) or isinstance(term,main.c.RVar):
            return []
    elif isinstance(term,main.c.Lambda):
            out += resolve(term.body)
    elif isinstance(term,main.c.Appl):
            out += resolve(term.func)
            out += resolve(term.arg)
    elif isinstance(term,main.c.Const):
            if term.pronoun == False:
                return []
            else:
                while True:
                    ques = 'What does \'' + term.name + '\' refer to? Type \'i\' for intensional.\n'
                    name=input(ques)
                    printtofile(ques[:-1],True,False)
                    printtofile(name,True,False)
                    try:
                        if name[0:2] == 'i ':  # intensional
                            repl = main.fullparse(name[2:])
                            intens = True
                        else:
                            repl = main.fullparse(name)
                            intens = False
                    except main.c.Error as e:
                        print('Error: ' + e.value)
                        continue
                    triple = [[term.name,repl,intens]]
                    if isinstance(repl,main.c.Const) and repl.pronoun:
                        return triple
                    else:
                        morepro = resolve(repl)   # RECURSIVE STEP <<<
                        if morepro:
                            return [[triple[0],morepro]]
                    return triple
                
    elif isinstance(term,main.c.Where):
        out += resolve(term.body)
        for i in term.set:
            out += resolve(i.right)
    elif isinstance(term,main.c.That):
        out += resolve(term.that) #first that, then terms
        for i in term.terms:
            out += resolve(i)
    return out

class repl:
    def __init__(self, term,ass=None):
        if ass is None:
            ass = []
        self.term = term
        self.ass = ass
    def __repr__(self):
        return str(self.term)

        

def countpro(term):
    if isinstance(term,main.c.Const):
        return int(term.pronoun)
    elif isinstance(term,main.c.Appl):
        return countpro(term.func)+countpro(term.arg)
    elif isinstance(term,main.c.Lambda):
        return countpro(term.body)
    elif isinstance(term,main.c.Where):
        return countpro(term.body)+sum([countpro(i.right) for i in term.set])
    elif isinstance(term,main.c.That):
        return countpro(term.that)+sum([countpro(i) for i in term.terms])
    else:
        return 0

           
# reps = [pro, term, bool]
def replace_pro(reps,term,wh=True,vars=None):
    if not reps or reps == [[]]:
        return repl(term)
    s = set()

    def build_set(l):
        if isinstance(l[0],list):
            build_set(l[0])
            for i in l[1]: build_set(i)
        else:
            s.add( (l[1],l[2]) )
    for i in reps:
        build_set(i)

    out = dict()
    if vars is not None:
        out = vars
    else:
        out = dict()
        for i in s:
            if not i[1]: # non-intens
                var = main.newvar('P',i[0].typ)
                out.update({i[0]:var})
            else:
                var = main.newfvar('p')
                out.update({i[0]:var})


    def replace_all(trm):
        if not isinstance(trm,repl):
            trm = repl(trm)
        t = trm.term
        a = trm.ass
        w = [[x[0],main.termeq(t,x[0])] for x in s if not x[1]]
        if any([x[1] for x in w]) and not getattr(t,'pronoun',False): # check if the term is equal to anything we are binding
            trm = [x[0] for x in w if x[1]][0]
            var = out[trm]
            return repl(var,a)
        else:
            if isinstance(t,main.c.PVar) or isinstance(t,main.c.RVar):
                return repl(t,a)
            elif isinstance(t,main.c.Lambda):
                x = replace_all(t.body)
                return repl(main.c.Lambda(t.var,x.term),x.ass)
            elif isinstance(t,main.c.Appl):
                f1 = replace_all(t.func)
                a1 = replace_all(t.arg)
                return repl(main.c.Appl(f1.term,a1.term),f1.ass+a1.ass)
            elif isinstance(t,main.c.Const):
                if t.pronoun:
                    u = reps.pop(0)
                    if isinstance(u[0],list):
                        #rec step
                        var = out[u[0][1]]
                        rec = replace_pro(u[1],u[0][1],False,out)
                        ttt = main.c.Fint(rec.term) if u[0][2] else rec.term
                        newa= a + [main.c.Assignment( var,  ttt)] + rec.ass
                        return repl(var,newa)
                        
                    else:
                        var = out[u[1]]
                        ttt = main.c.Fint(u[1]) if u[2] else u[1]
                        newa = a+[main.c.Assignment( var, ttt )]
                        return repl(var,newa)
                else:
                    return repl(t,a)
            elif isinstance(t,main.c.Where):
                lst = [main.c.Assignment(i.left,replace_all(i.right).term) for i in t.set]
                return repl(main.c.Where(replace_all(t.body).term,lst),a)
            elif isinstance(t,main.c.That):
                w2 = [[x[0],main.termeq(t.that, x[0])] for x in s if x[1]]
                newa = []
                if any([x[1] for x in w2]):
                    v = out[[x[0] for x in w2 if x[1]][0]]
                    num = countpro(t.that) # count pronouns
                    [reps.pop(0) for i in range(num)] #  <<<< delete the right number of pronouns from reps !
                else:
                    v1 = replace_all(t.that)
                    newa += v1.ass
                    v = v1.term
                lst = [replace_all(i) for i in t.terms]
                for i in lst: newa += i.ass
                lst2 = [j.term for j in lst]
               
                return repl(main.c.That(t.const,v,*lst2),newa)


    new = repl(term)
    rr = replace_all(new)

    for i in rr.ass:
            for j in rr.ass:
                if j!= i and main.termeq(j,i):
                    rr.ass.remove(j)
    if wh:
        final = main.c.Where(rr.term,set(rr.ass))
        rr.term = final
        return rr
    else:
        return rr
        
sfile = []
def printtofile(s, tofile=True,toprint=True):
    global sfile
    if toprint: print(s)
    if tofile: sfile.append(s)

def prty(s, onset=0):
    if len(s)<2:
        return str(s)
    count = 0
    for i in s:
        if count == 0:
            k = '{' + str(i) + ',\n'
        elif count == len(s)-1:
            k += onset * ' ' + str(i) + '}'
        else:
            k += onset * ' '+ str(i) + ',\n'
        count += 1
    return k


# def pretty_print(f):
#     if isinstance(f,main.c.Where):
#         bd = f.body
#         if isisntance(bd,main.c.Lambda) or isinstance(bd,main.c.Where):
#             h = '(' + str(bd) + ')'
#         else:
#             h = str(bd)
#         
#         w = len(h)
#         return w + prty(f.set,len(h)+8)
#     else:
#         return f
proh = ['(ap)','(recap)']

def strlist(l):
    m = [x for x in l if x != '']
    if not m:
        return ''
    out = str(m[0])
    for i in m[1:]:
        out += '; ' + str(i)
    return out

def wrap(t):
    if isinstance(t,main.c.Where) or isinstance(t,main.c.Lambda):
        return '(' + str(t) + ')'
    else:
        return str(t)

def verb(l,lvl):
    out = [[l[0][0]]]
    cf = False
    if lvl == 0:
        return l
    else:
        for i,z in enumerate(l[:-1]):
            lab = [x for x in z[1] if x not in proh ]
            if lab:
                out[-1].append(z[1])
                out.append([l[i+1][0]])
                if i == len(l)-2:
                    cf = True
        if not cf:
            out[-1].append('0')
            out.append(l[-1])
    return out 

def splitby(string,n):
    s = string
    out = []
    while len(s)>n:
        k = s[:n].rfind(',') #find last comma
        if k==-1: #no comma
            out.append(s[:n])
            s = s[n:]
        else:
            out.append(s[:k+1])
            s = s[k+1:]
    out.append(s)

    return out


def pretty_print(l,lvl=0):
    v = verb(l,lvl)
    def prty(t,onset=0):
        if isinstance(t,main.c.Where):
            if len(t.set)==1:
                prn = str(t)
                if len(prn) > maxlen:
                    first = '\n'.join(splitby(wrap(t.body),maxlen)) + '\n'
                    first += '   where ' + '\n'.join(splitby(str(t.set),maxlen))
                    return first
                else:
                    return prn
            else:
                first = '\n'.join(splitby(wrap(t.body),maxlen)) + '\n'
                m = 8+onset
                cnt = 0
                for x in t.set:
                    if cnt == 0:
                        out = first + ' where {' + str(x) + ',\n'
                    else:
                        out += ' '*m+str(x)+',\n'
                    cnt += 1
                out = out[:-2] + '}'
        else:
            ln = str(t)
            out = '\n'.join(splitby(ln,maxlen))
        return out
    
    if lvl==2: #only CF
        printtofile(prty(l[0][0]))
        printtofile('CF: ' + prty(l[-1][0],4))
    else:
        printtofile(prty(v[0][0]))
        for i in range(1,len(v)):
            if pause:
                while True:
                    getch = _Getch()
                    key = chr(ord(getch.impl()))
                    if key == "\r": #Return
                        cont = True
                        break
                    elif key == "q":
                        cont = False
                        break
                    else:
                        print('(press Enter for the next step, or q to quit)')
            else:
                cont = True
            if cont:
                printtofile('==> ' + strlist(v[i-1][1]))
                printtofile(prty(v[i][0]))
            else:
                break

try:
    main.readfile('SETTINGS')
except main.c.Error as e:
    print('Error: ' + e.value)
    sys.exit()


filename = args.filename
try:
    main.readfile(filename)
    lfs = main.lfs
except main.c.Error as e:
    print('Error: ' + e.value)
    sys.exit()
num = 1

if not lfs:
    print('No LFs given!')
    sys.exit()


numb = len(lfs)
for z,i in enumerate(lfs):
    try:
        if i[0:5] == 'echo ':
            printtofile(i[5:])
            continue
        elif i[0:1] == '@':
            if i[1:14] == 'maxlinelength':
                try:
                    maxlen = int(i[15:])
                except ValueError:
                    print('Error: invalid line length specification')
            continue   
        else:
            main.c.typed = True
            lf = main.fullparse(i)
            main.c.typed = False
    except main.c.Error as e:
        print('Parse error: ' + e.value)
        sys.exit()
    try:
        #red = main.fullreduce_print(lf)
        printtofile('LF '+str(num)+': ' + str(lf))
        lf1 = replace_pro(resolve(lf),lf) #resolve pronouns
        if isinstance(lf1,repl):
            lf1 = lf1.term
        lf2 = main.rename(lf1) #rename variables
  
        red = main.printlist(main.recreduce(lf2))
    except main.c.Error as e:
        print('Error: ' + e.value)
        sys.exit()

    pretty_print(red.form,vrb)
    if red.lem and not vrb==2:
        for i in red.lem:
            vv = verb(i.form,vrb)
            if len(vv) > 1:
                printtofile('\nLemma\n-----')
                pretty_print(vv,vrb)
            else:
                printtofile('\nLemma: already in CF:')
                pretty_print(vv,vrb)
    if pause and not z==numb-1:
        while True:
            getch = _Getch()
            key = chr(ord(getch.impl()))
            if key == "\r": #Return
                break
            else:
                print('(press Enter for the next LF)')    
    
#     for i in red:
#        # print('====> ' + str(i[1]))
#         #print(pretty_print(i[0]))
#         #x = input('...')
#         #if x == 'q':
#          #   break
#         while True:
#             getch = _Getch()
#             if getch.impl() == "\r": #Return
#                 cont = True
#                 break
#             elif getch.impl() == "q":
#                 cont = False
#                 break
#         if cont:
#             continue
#         else:
#             break
           
    printtofile('\n')
    main.c.clearstack()
    main.starred = set()
    
    num+= 1


def write_file(fn,strlist):
    f = open(fn,'w')
    for i in strlist:
        f.write(i + '\n')
    print('Output written to ' + fn)
    f.close()

if output_to_file is not None:
    while os.path.isfile(output_to_file):
        q=input(output_to_file + ' exists. Overwrite file? [y/n]\n')
        if q == 'y':
            break
        elif q == 'n':
            r = input('Type new filename\n')
            output_to_file = r
            
    write_file(output_to_file,sfile)


sys.exit()
