import sys
import subprocess

#A snake is a list of '0' and '1' where a '0' means
#	      that the block is a line and '1' a turn
#A cube is a 3D matrix filled with number of blocks 
#	    of the snake for each cell
#ex: in 2x2x2 cube: snake can be 01111110 and the
#    associated cube is
#	 12
#	 43	
#										
#	 56
#	 87
#
# With this code, we can only check cubes of size 3 and 4 
#(1 and 2 are trivial)


#input : a file name with the snake 
#output : a list with 0 and 1 elements present in the file
def read_file(filename):
	myfile = open(filename, 'r')
	snake = []
	for line in myfile:
		for element in line:
			if (element == '0' or element == '1'):
				snake.append(int(element))
	return snake

#input: -myfile: name of the file where to write the snake
#		-snake: snake to write 
def print_snake(myfile, snake):
	for element in snake:
		myfile.write(str(element)+" ")
	myfile.write("\n")

#input: -myfile: name of the file where to write the cube
#		-cube: cube to write 
def print_cube(myfile, cube):
	
	if cube == []:
		myfile.write("impossible to make a cube\n")
		return
	it = 0
	cube_size = len(cube)
	for face in cube:
		for line in face:
			for i in range(cube_size*3+1):
				myfile.write("-")
			myfile.write("\n")
			for number in line:
				myfile.write("|")
				if number<10:
					myfile.write(" ")
				myfile.write(str(number))
			myfile.write("|\n")
			it += 1
			if it == cube_size:
				it = 0
				for i in range(cube_size*3+1):
					myfile.write("-")
				myfile.write("\n")

#input: size of the cube
#output: number of clauses for a cube of size 'cube_size'
def nb_constraints(cube_size):
	nb_cell = cube_size**3
	if cube_size == 3:
		symmetry_cstr = 18
	else:
		symmetry_cstr = 17
	nb_constraint = 1/2*nb_cell**3+3/2*nb_cell**2-2*nb_cell + symmetry_cstr
	return nb_constraint

#input: -myfile: name of file where to write constraints
#		-snake: the snake gives constraints       
def constraints(myfile, snake):

	def output(s):
		myfile.write(s)
	
	#i,j,k: cell in the cube (1->cube_size), l: block of the snake (11->11+cube_size^3)
	def newlit(i,j,k,l):
		output(str(i)+str(j)+str(k)+str(l)+" ")

	def newcl():
		output("0\n")

	def newcomment(s):
		output("c %s\n"%s)
	
	snake_length = len(snake)
	cube_size = round(snake_length**(1/3))

	#symmetry of the cube
	if cube_size == 3:
		#first element
		newlit(1,1,1,11)
		newlit(2,1,1,11)
		newlit(2,2,1,11)
		newlit(2,2,2,11)
		newcl()

		#second element
		output("-")
		newlit(1,1,1,11)
		newlit(1,1,2,12)
		newcl()

		output("-")
		newlit(2,1,1,11)
		newlit(2,1,2,12)
		newlit(1,1,1,12)
		newcl()

		output("-")
		newlit(2,2,1,11)
		newlit(2,2,2,12)
		newlit(2,1,1,12)
		newcl()

		output("-")
		newlit(2,2,2,11)
		newlit(2,2,1,12)
		newcl()

		#third element
		output("-")
		newlit(1,1,1,11)
		newlit(1,1,3,13)
		newlit(1,2,2,13)
		newcl()

		output("-")
		newlit(2,1,1,11)
		output("-")
		newlit(2,1,2,12)
		newlit(2,1,3,13)
		newlit(1,1,2,13)
		newlit(2,2,2,13)
		newcl()

		output("-")
		newlit(2,1,1,11)
		output("-")
		newlit(1,1,1,12)
		newlit(1,1,2,13)
		newcl()

		output("-")
		newlit(2,2,1,11)
		output("-")
		newlit(2,2,2,12)
		newlit(2,2,3,13)
		newlit(2,1,2,13)
		newcl()

		output("-")
		newlit(2,2,1,11)
		output("-")
		newlit(2,1,1,12)
		newlit(1,1,1,13)
		newlit(2,1,2,13)
		newcl()

		output("-")
		newlit(2,2,2,11)
		output("-")
		newlit(2,2,1,12)
		newlit(1,2,1,13)
		newcl()

		#fourth element
		output("-")
		newlit(1,1,1,11)
		output("-")
		newlit(1,1,2,12)
		output("-")
		newlit(1,1,3,13)
		newlit(2,1,3,14)
		newcl()

		output("-")
		newlit(2,1,1,11)
		output("-")
		newlit(2,1,2,12)
		output("-")
		newlit(2,1,3,13)
		newlit(2,2,3,14)
		newlit(1,1,3,14)
		newcl()

		output("-")
		newlit(2,1,1,11)
		output("-")
		newlit(2,1,2,12)
		output("-")
		newlit(2,2,2,13)
		newlit(2,2,1,14)
		newlit(2,2,3,14)
		newlit(2,3,2,14)
		newlit(1,2,2,14)
		newcl()

		output("-")
		newlit(2,2,1,11)
		output("-")
		newlit(2,2,2,12)
		output("-")
		newlit(2,2,3,13)
		newlit(1,2,3,14)
		newcl()

		output("-")
		newlit(2,2,1,11)
		output("-")
		newlit(2,2,2,12)
		output("-")
		newlit(1,2,2,13)
		newlit(1,2,1,14)
		newlit(1,2,3,14)
		newlit(1,1,2,14)
		newcl()

		output("-")
		newlit(2,2,1,11)
		output("-")
		newlit(2,1,1,12)
		output("-")
		newlit(2,1,2,13)
		newlit(2,1,3,14)
		newlit(2,2,2,14)
		newlit(1,1,2,14)
		newcl()

		output("-")
		newlit(2,2,2,11)
		output("-")
		newlit(2,2,1,12)
		output("-")
		newlit(1,2,1,13)
		newlit(1,2,2,14)
		newlit(1,1,1,14)
		newcl()

		#fifth element (10 possibles new clauses and more for sixth, ...)
	else:
		#first element
		newlit(1,1,1,11)
		newlit(2,1,1,11)
		newlit(2,2,1,11)
		newlit(2,2,2,11)
		newcl()

		#second element
		output("-")
		newlit(1,1,1,11)
		newlit(1,1,2,12)
		newcl()

		output("-")
		newlit(2,1,1,11)
		newlit(2,1,2,12)
		newlit(1,1,1,12)
		newlit(3,1,1,12)
		newcl()

		output("-")
		newlit(2,2,1,11)
		newlit(2,2,2,12)
		newlit(2,1,1,12)
		newlit(3,2,1,12)
		newcl()

		output("-")
		newlit(2,2,2,11)
		newlit(2,2,1,12)
		newlit(3,2,2,12)
		newcl()

		#third element
		output("-")
		newlit(1,1,1,11)
		output("-")
		newlit(1,1,2,12)
		newlit(1,1,3,13)
		newlit(1,2,2,13)
		newcl()

		output("-")
		newlit(2,1,1,11)
		output("-")
		newlit(1,1,1,12)
		newlit(1,1,2,13)
		newcl()

		output("-")
		newlit(2,1,1,11)
		output("-")
		newlit(3,1,1,12)
		newlit(4,1,1,13)
		newlit(3,1,2,13)
		newcl()

		output("-")
		newlit(2,2,1,11)
		output("-")
		newlit(2,2,2,12)
		newlit(2,1,2,13)
		newlit(2,2,3,13)
		newlit(3,2,2,13)
		newcl()

		output("-")
		newlit(2,2,2,11)
		output("-")
		newlit(2,2,1,12)
		newlit(1,2,1,13)
		newlit(3,2,1,13)
		newcl()

		output("-")
		newlit(2,2,2,11)
		output("-")
		newlit(3,2,2,12)
		newlit(3,1,2,13)
		newlit(3,2,3,13)
		newlit(4,2,2,13)
		newcl()

		#fourth element
		output("-")
		newlit(1,1,1,11)
		output("-")
		newlit(1,1,2,12)
		output("-")
		newlit(1,1,3,13)
		newlit(1,1,4,14)
		newlit(2,1,3,14)
		newcl()

		output("-")
		newlit(2,1,1,11)
		output("-")
		newlit(3,1,1,12)
		output("-")
		newlit(4,1,1,13)
		newlit(4,1,2,14)
		newcl()

		output("-")
		newlit(2,2,1,11)
		output("-")
		newlit(2,2,2,12)
		output("-")
		newlit(2,2,3,13)
		newlit(2,2,4,14)
		newlit(2,1,3,14)
		newlit(3,1,3,14)
		newcl()

		output("-")
		newlit(2,2,2,11)
		output("-")
		newlit(3,2,2,12)
		output("-")
		newlit(4,2,2,13)
		newlit(4,2,1,14)
		newlit(4,2,3,14)
		newcl()

		#fifth element
		output("-")
		newlit(1,1,1,11)
		output("-")
		newlit(1,1,2,12)
		output("-")
		newlit(1,1,3,13)
		output("-")
		newlit(1,1,4,14)
		newlit(2,1,4,15)
		newcl()

		output("-")
		newlit(2,2,1,11)
		output("-")
		newlit(2,2,2,12)
		output("-")
		newlit(2,2,3,13)
		output("-")
		newlit(2,2,4,14)
		newlit(2,1,4,15)
		newlit(3,2,4,15)
		newcl()

	#at least one block per cube cell
	for i in range(1,cube_size+1):
		for j in range(1,cube_size+1):
			for k in range(1,cube_size+1):
				for l in range(1,snake_length+1):
					newlit(i,j,k,l+10)
				newcl()

	#each block at most once
	for l in range(1,snake_length+1):
		for i in range(1,cube_size+1):
			for j in range(1,cube_size+1):
				for k in range(1,cube_size+1):
					for m in range(1,cube_size+1):
						for n in range(1,cube_size+1):
							for o in range(1,cube_size+1):
								if m < i:
									continue
								if m == i:
									if n < j:
										continue
									if n == j:
										if o <= k:
											continue
								output("-")
								newlit(i,j,k,l+10)
								output("-")
								newlit(m,n,o,l+10)
								newcl()

	#each block next to the next one in the cube 
	for l in range(1,snake_length):
		for i in range(1,cube_size+1):
			for j in range(1,cube_size+1):
				for k in range(1,cube_size+1):
					output("-")
					newlit(i,j,k,l+10)
					if(i>1):
						newlit(i-1,j,k,l+11)
					if(i<cube_size):
						newlit(i+1,j,k,l+11)
					if(j>1):
						newlit(i,j-1,k,l+11)
					if(j<cube_size):
						newlit(i,j+1,k,l+11)
					if(k>1):
						newlit(i,j,k-1,l+11)
					if(k<cube_size):
						newlit(i,j,k+1,l+11)
					newcl()

	#constraints of the snake
	it = 10
	for digit in snake:
		it += 1
		if (it == 11 or it == snake_length+10):
			continue
		if digit == 0:
			for i in range(1,cube_size+1):
				for j in range(1,cube_size+1):
					for k in range(1,cube_size+1):
						output("-")
						newlit(i,j,k,it-1)
						if(i>2):
							newlit(i-2,j,k,it+1)
						if(i<cube_size-1):
							newlit(i+2,j,k,it+1)
						if(j>2):
							newlit(i,j-2,k,it+1)
						if(j<cube_size-1):
							newlit(i,j+2,k,it+1)
						if(k>2):
							newlit(i,j,k-2,it+1)
						if(k<cube_size-1):
							newlit(i,j,k+2,it+1)
						newcl()
		else:
			for i in range(1,cube_size+1):
				for j in range(1,cube_size+1):
					for k in range(1,cube_size+1):
						output("-")
						newlit(i,j,k,it-1)
						if(i>1 and j>1):
							newlit(i-1,j-1,k,it+1)
						if(i>1 and j<cube_size):
							newlit(i-1,j+1,k,it+1)
						if(i>1 and k>1):
							newlit(i-1,j,k-1,it+1)
						if(i>1 and k<cube_size):
							newlit(i-1,j,k+1,it+1)
						if(i<cube_size and j>1):
							newlit(i+1,j-1,k,it+1)
						if(i<cube_size and j<cube_size):
							newlit(i+1,j+1,k,it+1)
						if(i<cube_size and k>1):
							newlit(i+1,j,k-1,it+1)
						if(i<cube_size and k<cube_size):
							newlit(i+1,j,k+1,it+1)
						if(j>1 and k>1):
							newlit(i,j-1,k-1,it+1)
						if(j>1 and k<cube_size):
							newlit(i,j-1,k+1,it+1)
						if(j<cube_size and k>1):
							newlit(i,j+1,k-1,it+1)
						if(j<cube_size and k<cube_size):
							newlit(i,j+1,k+1,it+1)
						newcl()


#input: -filename: name of the cnf file
#       -cube_size: size of the cube
#       -phase: selection strategy (string)
#output: -cube: a cube that satisfies constraints
# 	     -time: wall clock time in second for the sat solver
def cube_solve(filename, cube_size, phase):
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
            	return [], time
            continue
        if line[0] == 'v':
            line = line[2:]
            units = line.split()
            if units.pop() != '0':
                exit("strange output from SAT solver:" + line + "\n")
            units = [int(x) for x in units if int(x) >= 0]
            cube = [[[0 for i in range(cube_size)] for j in range(cube_size)] for k in range(cube_size)]
            for number in units:
            	cube[(number//10000)-1][(number//1000)%10-1][(number//100)%10-1] = number%100-10
            return cube, time
        exit("strange output from SAT solver:" + line + "\n")
        return [], time


# start of the main code
# first arg: name of the file that contains the snake
# second arg: selection strategy (Positive or Negative), nothing if default strategy
if len(sys.argv) < 2:
	exit("argument missing: filename")

snake = read_file(str(sys.argv[1]))
snake_length = len(snake)
cube_size = round(snake_length**(1/3))

if(cube_size**3 != snake_length):
	exit("snake length should be a power of 3")

print_snake(sys.stdout, snake)

#if there is more than (cube size - 2) '0' in a row in the snake
#(first and last 0 don't count), cube is impossible
nb_0 = -1
it = 1
for digit in snake:
	if digit == 0:
		nb_0 += 1
		if (nb_0 == (cube_size-1) and it < snake_length):
			exit("impossible to make a cube\n")
	else:
		nb_0 = 0
	it += 1

myfile = open("cube.cnf", 'w')
myfile.write("p cnf "+str(cube_size)+str(cube_size)+str(cube_size)+str(snake_length+10)+" "+
            str(nb_constraints(cube_size))+"\n")
constraints(myfile, snake)
myfile.close()  

if len(sys.argv) == 2:
    phase = ""
else:
    phase = sys.argv[2]
    
cube, time = cube_solve("cube.cnf", cube_size, phase) 
print_cube(sys.stdout, cube)
print("Solution found in " + time + " seconds")