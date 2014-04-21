import java.io.{IOException, RandomAccessFile}
import scala.io.Source


val PairRe = """\s*(\d+) \|-> \("(\d+)":Byte\)""".r
val DefineRe = """Definition (\w+) : Map_N_Byte := \[(.*)\]\.""".r

if (args.length < 2) {
  println("Not enough arguments")
  println("Usage:")
  println("\tscala byteCheck.scala input.v drive.dd [partialName]")
  println("\t\tinput.v is a Coq file to read from")
  println("\t\tdrive.dd is a file to compare against")
  println("\t\tpartialName is the name of the partial definition in input.v.")
  println("\t\t\tDefaults to the first matching definition")
  System.exit(1)
}

val inputFile = Source.fromFile(args(0))
val defines = for {DefineRe(name, contents) <- inputFile.getLines}
              yield (name, contents)
val relevantDefines = if (args.length > 2) defines.filter(_._1 == args(2))
                      else defines.take(1)

if (!relevantDefines.hasNext)
  System.err.println("Warning: No partial image found. Check arguments?")

val toCheck = for {
  (name, contents) <- relevantDefines
  PairRe(offset, value) <- contents.split(""",\s*""")
} yield (offset.toInt, value.toInt.toByte)

if (!toCheck.hasNext)
  System.err.println("Warning: No bytes to match. Bad file format?")

val checkFile = new RandomAccessFile(args(1), "r")
val (correct, incorrect) = toCheck.partition{ case (offset, value) =>
  try {
    checkFile.seek(offset)
    checkFile.readByte == value
  } catch {
    case _:IOException => false
  }
}

if (!incorrect.hasNext) {
  println("TRUE")
  println("%d bytes checked".format(correct.length))
  System.exit(0)
} else {
  println("FALSE")
  val incorrectCount = incorrect.length
  println("%d/%d bytes incorrect".format(incorrectCount,
                                         incorrectCount + correct.length))
  System.exit(2)
}
inputFile.close()
checkFile.close()
