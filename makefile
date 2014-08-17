C = scalac -cp /jvm/asm.jar:. -J-Xmx2G
S = scala -cp /jvm/asm.jar:. -J-Xmx2G

default : scasm/Scasm.class

scasm/Scasm.class : Scasm.scala
	${C} Scasm.scala
