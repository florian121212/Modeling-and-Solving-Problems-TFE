import sys
import subprocess

#A snake is a string of '0' and '1' where a '0' means
#        that the block is a line and '1' a turn
#A rectangle is a 3D matrix filled with number of each  
#        rectangle of the snake for each cell of the rectangle
#        rectangle size is given in a 3 digits number
#        first is the length, second the heigth and last the depth
# ex: in a 2x2x3 rectangle: snake can be 01111111110 
#     and the associated rectangle is
#     1 2
#     4 3                                           
#   
#     5 6
#     8 7
#
#     9 10
#    12 11


#input : a file name with the snake 
#output : a list with 0 and 1 elements present in the file
def read_file(filename):
    myfile = open(filename, 'r')
    snake = []
    for line in myfile:
        for element in line:
            if (element== '0' or element == '1'):
                snake.append(int(element))
    return snake

#input: -myfile: name of the file where to write the snake
#       -snake: snake to write 
def print_snake(myfile, snake):
    for element in snake:
        myfile.write(str(element)+" ")
    myfile.write("\n")

#input: -myfile: name of the file where to write the rectangle
#       -rectangle: rectangle to write 
def print_rectangle(myfile, rectangle):
    if rectangle == []:
        myfile.write("impossible to make a rectangle\n")
        return
    it = 0
    d = len(rectangle)
    h = len(rectangle[0])
    l = len(rectangle[0][0])
    for face in rectangle:
        for line in face:
            for i in range(l*3+1):
                myfile.write("-")
            myfile.write("\n")
            for number in line:
                myfile.write("|")
                if number<10:
                    myfile.write(" ")
                myfile.write(str(number))
            myfile.write("|\n")
            it += 1
            if it == h:
                it = 0
                for i in range(l*3+1):
                    myfile.write("-")
                myfile.write("\n")

#input: size of the rectangle
#output: number of clauses for a rectangle of size 'rectangle_size'
def nb_constraints(rectangle_size):
    l = rectangle_size//100 
    h = (rectangle_size//10)%10
    d = rectangle_size%10
    nb_cell = l*h*d
    nb_constraint = 1/2*nb_cell**3+3/2*nb_cell**2-2*nb_cell
    return nb_constraint

#input: -myfile: name of file where to write constraints
#       -snake: the snake that gives constraints       
def constraints(myfile, snake, rectangle_size):

    def output(s):
        myfile.write(s)
    
#   i,j,k cell in the rectangle (1->3),
#   l block in the snake (11->11+nb_cell)
    def newlit(i,j,k,l):
        output(str(i)+str(j)+str(k)+str(l)+" ")

    def newcl():
        output("0\n")

    def newcomment(s):
        output("c %s\n"%s)
    
    snake_length = len(snake)
    le = rectangle_size//100 
    he = (rectangle_size//10)%10
    de = rectangle_size%10
    nb_cell = le*he*de
    
    #each block at least once
    for l in range(1,snake_length+1):
        for i in range(1,de+1):
            for j in range(1,he+1):
                for k in range(1,le+1):
                    newlit(i,j,k,l+10)
        newcl()

    #at most one block per rectangle cell
    for i in range(1,de+1):
        for j in range(1,he+1):
            for k in range(1,le+1):
                for l in range(1,snake_length):
                    for m in range(l+1, snake_length+1):
                        output("-")
                        newlit(i,j,k,l+10)
                        output("-")
                        newlit(i,j,k,m+10)
                        newcl()

    #each block next to the next one in the rectangle
    for l in range(1,snake_length):
        for i in range(1,de+1):
            for j in range(1,he+1):
                for k in range(1,le+1):
                    output("-")
                    newlit(i,j,k,l+10)
                    if(i>1):
                        newlit(i-1,j,k,l+11)
                    if(i<de):
                        newlit(i+1,j,k,l+11)
                    if(j>1):
                        newlit(i,j-1,k,l+11)
                    if(j<he):
                        newlit(i,j+1,k,l+11)
                    if(k>1):
                        newlit(i,j,k-1,l+11)
                    if(k<le):
                        newlit(i,j,k+1,l+11)
                    newcl()

    #constraints of the snake
    it = 10
    for digit in snake:
        it += 1
        if (it == 11 or it == snake_length+10):
            continue
        if digit == 0:
            for i in range(1,de+1):
                for j in range(1,he+1):
                    for k in range(1,le+1):
                        output("-")
                        newlit(i,j,k,it-1)
                        if(i>2):
                            newlit(i-2,j,k,it+1)
                        if(i<de-1):
                            newlit(i+2,j,k,it+1)
                        if(j>2):
                            newlit(i,j-2,k,it+1)
                        if(j<he-1):
                            newlit(i,j+2,k,it+1)
                        if(k>2):
                            newlit(i,j,k-2,it+1)
                        if(k<le-1):
                            newlit(i,j,k+2,it+1)
                        newcl()
        else:
            for i in range(1,de+1):
                for j in range(1,he+1):
                    for k in range(1,le+1):
                        output("-")
                        newlit(i,j,k,it-1)
                        if(i>1 and j>1):
                            newlit(i-1,j-1,k,it+1)
                        if(i>1 and j<he):
                            newlit(i-1,j+1,k,it+1)
                        if(i>1 and k>1):
                            newlit(i-1,j,k-1,it+1)
                        if(i>1 and k<le):
                            newlit(i-1,j,k+1,it+1)
                        if(i<de and j>1):
                            newlit(i+1,j-1,k,it+1)
                        if(i<de and j<he):
                            newlit(i+1,j+1,k,it+1)
                        if(i<de and k>1):
                            newlit(i+1,j,k-1,it+1)
                        if(i<de and k<le):
                            newlit(i+1,j,k+1,it+1)
                        if(j>1 and k>1):
                            newlit(i,j-1,k-1,it+1)
                        if(j>1 and k<le):
                            newlit(i,j-1,k+1,it+1)
                        if(j<he and k>1):
                            newlit(i,j+1,k-1,it+1)
                        if(j<he and k<le):
                            newlit(i,j+1,k+1,it+1)
                        newcl()


#input: -filename: name of the cnf file
#       -rectangle_size: size of the rectangle
#       -phase: selection strategy (string)
#output: -rectangle: a rectangle that satisfies constraints
#        -time: wall clock time in second for the sat solver
def rectangle_solve(filename, rectangle_size, phase):
    if phase == "":
        command = "java -jar sat4j-sat.jar "+ filename
    else:
        command = "java -jar sat4j-sat.jar -S PHASE=" + phase +"LiteralSelectionStrategy "+ filename  
    process = subprocess.Popen(command, shell=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = process.communicate()

    l = rectangle_size//100 
    h = (rectangle_size//10)%10
    d = rectangle_size%10

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
                print("unsatifiable")
                return [], time
            continue
        if line[0] == 'v':
            line = line[2:]
            units = line.split()
            if units.pop() != '0':
                exit("strange output from SAT solver:" + line + "\n")
            units = [int(x) for x in units if int(x) >= 0]
            rectangle = [[[0 for i in range(l)] for j in range(h)] for k in range(d)]
            for number in units:
                rectangle[(number//10000)-1][(number//1000)%10-1][(number//100)%10-1] = number%100-10
            return rectangle, time
        exit("strange output from SAT solver:" + line + "\n")
        return [], time


#start of the main code
# first arg: name of the file that contains the snake
# second arg: rectangle size xyz such that x <= y <= z
# third arg: selection strategy (Positive or Negative), nothing if default strategy
if len(sys.argv) < 2:
    exit("arguments missing: filename and rectangle size")

if len(sys.argv) < 3:
    exit("argument missing: rectangle size")

snake = read_file(str(sys.argv[1]))
l = int(sys.argv[2])//100 
h = (int(sys.argv[2])//10)%10
d = int(sys.argv[2])%10
nb_cell = l*h*d
snake_length = len(snake)
max_l = max(l,d,h)

if(nb_cell != snake_length):
    exit("snake length does not correspond to rectangle size")

print_snake(sys.stdout, snake)

#if there is more than depht-1 '0' in a row in the snake
#(first and last 0 don't count), rectangle is impossible
nb_0 = -1
it = 1
for digit in snake:
    if digit == 0:
        nb_0 += 1
        if (nb_0 == (max_l-1) and it < snake_length):
            exit("impossible to make a rectangle\n")
    else:
        nb_0 = 0
    it += 1

myfile = open("rectangle.cnf", 'w')
myfile.write("p cnf "+str(d)+str(h)+str(l)+str(snake_length+10)+" "+
            str(nb_constraints(int(sys.argv[2])))+"\n")
constraints(myfile, snake, int(sys.argv[2]))
myfile.close()

if len(sys.argv) == 3:
    phase = ""
else:
    phase = sys.argv[3]

rectangle, time = rectangle_solve("rectangle.cnf", int(sys.argv[2]), phase)
print_rectangle(sys.stdout, rectangle)
print("Solution found in " + time + " seconds")