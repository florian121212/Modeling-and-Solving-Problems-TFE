import sys
import subprocess
import math
# Othello nxn is a two-player game defined by a square grid board of nxn cells. 
#     States of the game are represented by tables black and white which contain coordinates 
#     of black and white tokens. Black is represented by 1 and white by 0, while space for a free cell.
#
#Initial state for a 6x6 board:
#
#     | | | | | | |
#     | | |1| | | |
#     | | |1|1| | |
#     | | |1|0| | |
#     | | | | | | |
#     | | | | | | |
# 

#input: -myfile: name of the file where to write the state
#       -black: cells with black tokens
#       -white: cells with white tokens 
#       -size: size of the board
def print_state(myfile, black, white, size):
    state = [[' ' for _ in range(size)] for _ in range(size)] 

    for coord in black:
        i, j = coord  
        state[i-1][j-1] = '1'  

    for coord in white:
        i, j = coord  
        state[i-1][j-1] = '0'

    print("black:1 \nwhite:0 \n\n")
    for i in range(len(state)):
        for j in range(len(state[i])):
            myfile.write("|"+ state[j][i])
            if j == len(state[i])-1:
                myfile.write("|\n")
    return

#input: -myfile: name of the file where to write the moves 
#       -moves: list of moves
def print_moves(myfile, moves): 
    print("\n")
    for move in moves:
        i,j,k = move
        if i == 1:
            myfile.write("black: (" + str(j) + ", " + str(k) + ")\n")
        else:
            myfile.write("white: (" + str(j) + ", " + str(k) + ")\n")
    return

#input: -end_state: maximum number of moves
#       -size: size of the board   
#output: number of clauses in the sat encoding 
def nb_constraints(end_state, size):
    
    S = size**2-5
    if (size == 5 or size == 7):
        S += 1

    if size == 4:
        nb_constraints = 31006
    elif size == 5:
        nb_constraints = 145418
    elif size == 6:
        nb_constraints = 444218
    elif size == 7:
        nb_constraints = 1187114
    else:
        nb_constraints = 2633838

    if end_state < S:
        nb_constraints += 1

    return nb_constraints

#input: -myfile: name of file where to write constraints   
#       -endgame: maximum number of moves 
#       -size: size of the board   
def constraints(myfile, end_state, size):

    S = size**2-5
    if (size == 5 or size == 7):
        S += 1

    def output(s):
        myfile.write(s)

#   s,c,r: state s(10->S+10), column c(1->size), row r(1->size)
    def black(s,c,r):
        output("3"+str(s)+str(c)+str(r)+"01 ")

#   s,c,r: state s(10->S+10), column c(1->size), row r(1->size)
    def white(s,c,r):
        output("3"+str(s)+str(c)+str(r)+"02 ")

#   s,c,r: state s(10->S+10), column c(1->size), row r(1->size)
    def occupied(s,c,r):
        output("3"+str(s)+str(c)+str(r)+"03 ")

#   s,c,r: state s(10->S+10), column c(1->size), row r(1->size)
    def bvalid(s,c,r):
        output("3"+str(s)+str(c)+str(r)+"04 ")

#   s,c,r: state s(10->S+10), column c(1->size), row r(1->size)
    def wvalid(s,c,r):
        output("3"+str(s)+str(c)+str(r)+"05 ")

#   s,c,r: state s(10->S+10), column c(1->size), row r(1->size)
    def bmove(s,c,r):
        output("3"+str(s)+str(c)+str(r)+"06 ")

#   s,c,r: state s(10->S+10), column c(1->size), row r(1->size)
    def wmove(s,c,r):
        output("3"+str(s)+str(c)+str(r)+"07 ")

#   s,c,r: state s(10->S+10), column c(1->size), row r(1->size)
    def bflip(s,c,r):
        output("3"+str(s)+str(c)+str(r)+"08 ")

#   s,c,r: state s(10->S+10), column c(1->size), row r(1->size)
    def wflip(s,c,r):
        output("3"+str(s)+str(c)+str(r)+"09 ")

#   s: state s(10->S+10)
    def bimpo(s):
        output("3"+str(s)+"0089 ")

#   s: state s(10->S+10)
    def wimpo(s):
        output("3"+str(s)+"0090 ")

#   s: state s(10->S+10)
    def turn(s):
        output("3"+str(s)+"0091 ")

#   s: state s(10->S+10)
    def endgame(s):
        output("3"+str(s)+"0092 ")

#   s,c1,r1,c2,r2: state s(10->S+10), column1 c1(1->size), row1 r1(1->size), column2 c2(1->size), row2 r2(1->size)
    def bline(s,c1,r1,c2,r2):
        output("2"+str(s)+str(c1)+str(r1)+str(c2)+str(r2)+" ")

#   s,c1,r1,c2,r2: state s(10->S+10), column1 c1(1->size), row1 r1(1->size), column2 c2(1->size), row2 r2(1->size)
    def wline(s,c1,r1,c2,r2):
        output("1"+str(s)+str(c1)+str(r1)+str(c2)+str(r2)+" ")

    def newcl():
        output("0\n")

    def newcomment(s):
        output("c %s\n"%s)

#   initial state (74 clauses)
    for c in range(1,size+1):
        for r in range(1,size+1):
            if (size == 5 or size == 7):
                if ((c==math.floor(size/2)+1 and r==math.floor(size/2)) or (c==math.floor(size/2) and r==math.floor(size/2)+1)):
                    black(10,c,r)
                    newcl()
                    output("-")
                    white(10,c,r)
                    newcl()
                elif ((c==math.floor(size/2) and r==math.floor(size/2)) or (c==math.floor(size/2)+1 and r==math.floor(size/2)+1)):
                    output("-")
                    black(10,c,r)
                    newcl()
                    white(10,c,r)
                    newcl() 
                else:
                    output("-")
                    black(10,c,r)
                    newcl()
                    output("-")
                    white(10,c,r)
                    newcl() 
            else:
                if ((c==math.floor(size/2) and r==math.floor(size/2)-1) or (c==math.floor(size/2) and r==math.floor(size/2)) 
                        or (c==math.floor(size/2) and r==math.floor(size/2)+1) or (c==math.floor(size/2)+1 and r==math.floor(size/2))):
                    black(10,c,r)
                    newcl()
                    output("-")
                    white(10,c,r)
                    newcl()
                elif (c==math.floor(size/2)+1 and r==math.floor(size/2)+1):
                    output("-")
                    black(10,c,r)
                    newcl()
                    white(10,c,r)
                    newcl() 
                else:
                    output("-")
                    black(10,c,r)
                    newcl()
                    output("-")
                    white(10,c,r)
                    newcl() 

    if (size == 5 or size == 7):
        turn(10)
        newcl()
    else:
        output("-")
        turn(10)
        newcl()

    output("-")
    endgame(10)
    newcl()

#   constraint1: occupied variable (3456 clauses)
    for s in range(10,S+11):
        for c in range(1,size+1):
            for r in range(1,size+1):
                black(s,c,r)
                white(s,c,r)
                output("-")
                occupied(s,c,r)
                newcl()

                output("-")
                black(s,c,r)
                occupied(s,c,r)
                newcl()

                output("-")
                white(s,c,r)
                occupied(s,c,r)
                newcl()

#   constraint2: black and white variables (8928 clauses)
    for s in range(11,S+11):
        for c in range(1,size+1):
            for r in range(1,size+1):
                wflip(s,c,r)
                bflip(s,c,r)
                output("-")
                black(s-1,c,r)
                black(s,c,r)
                newcl()
                
                wflip(s,c,r)
                bflip(s,c,r)
                output("-")
                black(s,c,r)
                black(s-1,c,r)
                newcl()

                output("-")
                bflip(s,c,r)
                black(s,c,r)
                newcl()

                output("-")
                wflip(s,c,r)
                output("-")
                black(s,c,r)
                newcl()

                wflip(s,c,r)
                bflip(s,c,r)
                output("-")
                white(s-1,c,r)
                white(s,c,r)
                newcl()
                
                wflip(s,c,r)
                bflip(s,c,r)
                output("-")
                white(s,c,r)
                white(s-1,c,r)
                newcl()

                output("-")
                wflip(s,c,r)
                white(s,c,r)
                newcl()

                output("-")
                bflip(s,c,r)
                output("-")
                white(s,c,r)
                newcl()

#   constraint3: bimpo and wimpo variables (2294 clauses)
    for s in range(10,S+10):
        for c in range(1,size+1):
            for r in range(1,size+1):
                bvalid(s,c,r)
        bimpo(s)
        if s>10:
            endgame(s-1)
        newcl()
        for c in range(1,size+1):
            for r in range(1,size+1):
                wvalid(s,c,r)
        wimpo(s)
        if s>10:
            endgame(s-1)
        newcl()
        for c in range(1,size+1):
            for r in range(1,size+1):
                output("-")
                bvalid(s,c,r)
                output("-")
                bimpo(s)
                endgame(s-1)
                newcl()

                output("-")
                wvalid(s,c,r)
                output("-")
                wimpo(s)
                endgame(s-1)
                newcl()
        
#   constraint4: turn variables (120 clauses)
    for s in range(11,S+10):
        turn(s-1)
        bimpo(s)
        turn(s)
        endgame(s-1)
        newcl()

        output("-")
        turn(s-1)
        output("-")
        wimpo(s)
        turn(s)
        endgame(s-1)
        newcl()

        output("-")
        turn(s-1)
        wimpo(s)
        output("-")
        turn(s)
        endgame(s-1)
        newcl()

        turn(s-1)
        output("-")
        bimpo(s)
        output("-")
        turn(s)
        endgame(s-1)
        newcl()

#   constraint5: endgame variable (120 clauses)
    for s in range(11,S+10):
        output("-")
        bimpo(s)
        output("-")
        wimpo(s)
        endgame(s)
        newcl()

        bimpo(s)
        output("-")
        endgame(s)
        newcl()

        wimpo(s)
        output("-")
        endgame(s)
        newcl()

        output("-")
        endgame(s-1)
        endgame(s)
        newcl()

#   constraint6: bmove and wmove variables (45818 clauses)
    for s in range(11,S+11):
        output("-")
        turn(s-1)
        endgame(s-1)
        for c in range(1,size+1):
            for r in range(1,size+1):
                bmove(s,c,r)
        newcl()

        turn(s-1)
        endgame(s-1)
        for c in range(1,size+1):
            for r in range(1,size+1):
                wmove(s,c,r)
        newcl()

        for c1 in range(1,size+1):
            for r1 in range(1,size+1):
                for c2 in range(1,size+1):
                    for r2 in range(1,size+1):
                        if ((r1 < r2) or (r1 == r2 and c1 < c2)):
                            output("-")
                            bmove(s,c1,r1)
                            output("-")
                            bmove(s,c2,r2)
                            newcl()

                            output("-")
                            wmove(s,c1,r1)
                            output("-")
                            wmove(s,c2,r2)
                            newcl()

        for c in range(1,size+1):
            for r in range(1,size+1):
                turn(s-1)
                output("-")
                bmove(s,c,r)
                newcl()

                output("-")
                endgame(s-1)
                output("-")
                bmove(s,c,r)
                newcl()

                bvalid(s-1,c,r)
                output("-")
                bmove(s,c,r)
                newcl()

                output("-")
                turn(s-1)
                output("-")
                wmove(s,c,r)
                newcl()

                output("-")
                endgame(s-1)
                output("-")
                wmove(s,c,r)
                newcl()

                wvalid(s-1,c,r)
                output("-")
                wmove(s,c,r)
                newcl()

#sets and dictionnary for the three last constraints

    #add the line starting in (c1,r1) and ending in (c2,r2) in the set 'lines'
    def newline(c1,c2,r1,r2,lines):
        line = []
        if (c1 == c2 and r1>r2):
            for i in range(r1-r2+1):
                line.append((c1,r1-i))
        elif (c1 == c2 and r1<r2):
            for i in range(r2-r1+1):
                line.append((c1,r1+i))
        elif (r1 == r2 and c1>c2):
            for i in range(c1-c2+1):
                line.append((c1-i,r1))
        elif (r1 == r2 and c1<c2):
            for i in range(c2-c1+1):
                line.append((c1+i,r1))
        elif (c1>c2 and r1>r2):
            for i in range(c1-c2+1):
                line.append((c1-i,r1-i))
        elif (c1>c2 and r1<r2):
            for i in range(c1-c2+1):
                line.append((c1-i,r1+i))
        elif (c1<c2 and r1>r2):
            for i in range(c2-c1+1):
                line.append((c1+i,r1-i))
        else:
            for i in range(c2-c1+1):
                line.append((c1+i,r1+i))

        lines.append(list(line))

#   add the line 'line' in the dictionary 'dico' with the key 'key'
    def add_line(dico, line, key):
        if key in dico:
            dico[key].append(line)
        else:
            dico[key] = [line]

#   add the cell 'cell' in the dictionary 'dico' with the key 'key'
    def add_cell(dico, cell, key):
        if key in dico:
            if cell not in dico[key]:
                dico[key].append(cell)
        else:
            dico[key] = [cell]


    lines = []
    for c1 in range(1,size+1):
        for r1 in range(1,size+1):
            for c2 in range(1,size+1):
                for r2 in range(1,size+1):
                    if ((c1 == c2 and abs(r1-r2)>=2) or (r1 == r2 and abs(c1-c2)>=2) or (abs(c1-c2) == abs(r1-r2) and abs(c1-c2)>=2)):
                        newline(c1,c2,r1,r2,lines)

    lineof = {}
    linewith = {}
    inlineof = {}
    for line in lines:
        add_line(lineof, line, line[0])
        for cell in line:
            add_line(linewith, line, cell)
            add_cell(inlineof, cell, line[0])

#   constraint7: bline and wline variables (109120 clauses)
    for s in range(10,S+10):
        for line in lines:
            occupied(s,line[0][0],line[0][1])
            for i in range(1,len(line)-1):
                output("-")
                white(s,line[i][0],line[i][1])
            output("-")
            black(s,line[len(line)-1][0],line[len(line)-1][1])
            bline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
            newcl()

            occupied(s,line[0][0],line[0][1])
            for i in range(1,len(line)-1):
                output("-")
                black(s,line[i][0],line[i][1])
            output("-")
            white(s,line[len(line)-1][0],line[len(line)-1][1])
            wline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
            newcl()

            output("-")
            occupied(s,line[0][0],line[0][1])
            output("-")
            bline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
            newcl()

            black(s,line[len(line)-1][0],line[len(line)-1][1])
            output("-")
            bline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
            newcl()

            output("-")
            occupied(s,line[0][0],line[0][1])
            output("-")
            wline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
            newcl()

            white(s,line[len(line)-1][0],line[len(line)-1][1])
            output("-")
            wline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
            newcl()

            for i in range(1,len(line)-1):
                white(s,line[i][0],line[i][1])
                output("-")
                bline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
                newcl()

                black(s,line[i][0],line[i][1])
                output("-")
                wline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
                newcl()

#   constraint8: bvalid and wvalid variables (24552 clauses)
    for s in range(10,S+10):
        for c in range(1,size+1):
            for r in range(1,size+1):
                for line in lineof[(c,r)]:
                    bline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
                output("-")
                bvalid(s,c,r)
                newcl()

                for line in lineof[(c,r)]:
                    wline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
                output("-")
                wvalid(s,c,r)
                newcl()

                for line in lineof[(c,r)]:
                    output("-")
                    bline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
                    bvalid(s,c,r)
                    newcl()

                    output("-")
                    wline(s,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
                    wvalid(s,c,r)
                    newcl()

#   constraint9: bflip and wflip variables (249736 clauses)
    for s in range(11,S+11):
        for c in range(1,size+1):
            for r in range(1,size+1):
                for c1 in range(1,size+1):
                    for r1 in range(1,size+1):
                        if (c1,r1) in inlineof[(c,r)]:
                            for line in lineof[(c,r)]:
                                if line in linewith[(c1,r1)]:
                                    bline(s-1,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
                            output("-")
                            bmove(s,c,r)
                            output("-")
                            bflip(s,c1,r1)
                            newcl()

                            for line in lineof[(c,r)]:
                                if line in linewith[(c1,r1)]:
                                    wline(s-1,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
                            output("-")
                            wmove(s,c,r)
                            output("-")
                            wflip(s,c1,r1)
                            newcl()

                        else:
                            output("-")
                            bmove(s,c,r)
                            output("-")
                            bflip(s,c1,r1)
                            newcl()

                            output("-")
                            wmove(s,c,r)
                            output("-")
                            wflip(s,c1,r1)
                            newcl()

                        output("-")
                        wmove(s,c,r)
                        output("-")
                        bflip(s,c1,r1)
                        newcl()

                        output("-")
                        bmove(s,c,r)
                        output("-")
                        wflip(s,c1,r1)
                        newcl()

                for line in lineof[(c,r)]:
                    for i in range(len(line)):
                        output("-")
                        bmove(s,c,r)
                        output("-")
                        bline(s-1,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
                        bflip(s,line[i][0],line[i][1])
                        newcl()

                        output("-")
                        wmove(s,c,r)
                        output("-")
                        wline(s-1,line[0][0],line[0][1],line[len(line)-1][0],line[len(line)-1][1])
                        wflip(s,line[i][0],line[i][1])
                        newcl()

                output("-")
                endgame(s-1)
                output("-")
                bflip(s,c,r)
                newcl()

                output("-")
                endgame(s-1)
                output("-")
                wflip(s,c,r)
                newcl()

    if end_state < (S):
        endgame(end_state+10)


#input: -filename: name of cnf file
#       -phase: selection strategy (string)
#       -size: size of the board 
#output: -moves: list of moves
#        -black: cells with black tokens at the end
#        -white: cells with white tokens at the end
#        -time: wall clock time in second for the sat solver
def othello_solve(filename, phase, size):
    if phase == "":
        command = "java -jar sat4j-sat.jar "+ filename
    else:
        command = "java -jar sat4j-sat.jar -S PHASE=" + phase +"LiteralSelectionStrategy "+ filename  
    process = subprocess.Popen(command, shell=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = process.communicate()
    
    out_split = out.split(b'\r\n')
    out_split.pop()
    time = out_split.pop()
    time = time.split(b' ').pop()
    time = time.decode("utf-8")

    for line in out.split(b'\n'):
        line = line.decode("utf-8")
        if line == "" or line[0] == 'c':
            continue
        line = line.strip()
        if line[0] == 's':
            if line != 's SATISFIABLE':
                print("unsatisfiable")
                return [],[],[],time
            continue
        if line[0] == 'v':
            line = line[2:]
            units = line.split()
            if units.pop() != '0':
                exit("strange output from SAT solver:" + line + "\n")
            units = [int(x) for x in units if int(x) >= 0]

            black=[]
            white=[]
            moves=[]

            S = size**2-5
            if (size == 5 or size == 7):
                S += 1

            for number in units:
                if ((number%100) == 1 and (number//10000)%100 == (S+10)):
                    c = (number//1000)%10
                    r = (number//100)%10
                    black.append((c,r))
                elif ((number%100) == 2 and (number//10000)%100 == (S+10)):
                    c = (number//1000)%10
                    r = (number//100)%10
                    white.append((c,r))
                elif ((number%100) == 6):
                    c = (number//1000)%10
                    r = (number//100)%10
                    moves.append((1,c,r))
                elif ((number%100) == 7):
                    c = (number//1000)%10
                    r = (number//100)%10
                    moves.append((0,c,r))

            return moves,black,white,time
            
        exit("strange output from SAT solver:" + line + "\n")
        return [],[],[],time


# start of the main code
# first arg: size of the board (between 4 and 8 included)
# second arg: maximum number of move (between 0 and size**2-5) (optional)
# third arg: selection strategy (Positive or Negative), nothing if default strategy (optional)

if (len(sys.argv) < 2):
    exit("argument missing: size of the board")

if (int(sys.argv[1]) < 4):
    size = 4
elif(int(sys.argv[1]) > 8):
    size = 8
else:
    size = int(sys.argv[1])

S = size**2-5
if (size == 5 or size == 7):
    S += 1

if (len(sys.argv) > 2 and int(sys.argv[2]) > 0):
    end_state = int(sys.argv[2])
else:
    end_state = S

myfile = open("othello.cnf", 'w')
myfile.write("p cnf "+"3"+str(S+10)+str(size)+str(size)+"09 "+str(nb_constraints(end_state, size))+"\n")
constraints(myfile, end_state, size)
myfile.close()

if len(sys.argv) < 4:
    phase = ""
else:
    phase = sys.argv[3]

print("start solving\n")
moves,black,white,time = othello_solve("othello.cnf", phase, size)
print("end solving\n")
print_state(sys.stdout, black, white, size)
print_moves(sys.stdout, moves)
print("Solution found in " + time + " seconds")