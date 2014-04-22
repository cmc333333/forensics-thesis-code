import java.io.{FileOutputStream, RandomAccessFile}
import scala.io.Source


type BA = Int

case class SuperBlock(inodesCount:Int, inodesPerGroup:Int, blockSize:Int) { 
  def toOffset(ba:BA):Int = blockSize * ba
}

case class Inode(size:Int, block:List[BA])

case class Image(file:RandomAccessFile, shift:Long=0l) {
  //  Note that this doesn't account for overflow
  def lendu(offset:Long) = {
    file.seek(shift + offset)
    val buffer = new Array[Byte](4)
    file.read(buffer)
    var result = 0
    result = result | ((buffer(3) & 0xff) << 24)
    result = result | ((buffer(2) & 0xff) << 16)
    result = result | ((buffer(1) & 0xff) << 8)
    result = result | ((buffer(0) & 0xff) << 0)
    result
  }
}

def directBlocks(inodeImg:Image):Seq[BA] = for (i <- 0 to 11) yield {
  inodeImg.lendu(40 + 4*i)
}

def indirectBlocks(img:Image, sb:SuperBlock, start:Long):Seq[BA] = 
  for (i <- 0 until (sb.blockSize/4)) yield img.lendu(start + i*4)

def readDataBlock(file:RandomAccessFile, ba:BA, superblock:SuperBlock,
                  size:Int) = {
  val buffer = new Array[Byte](superblock.blockSize)
  file.seek(superblock.toOffset(ba))
  file.read(buffer, 0, size)
  buffer
}

def writeData(file:RandomAccessFile, inodeIndex:Int,
              writeTo:FileOutputStream) = {
  val img = Image(file)
  val sbImg = img.copy(shift=1024l)
  val superblock = SuperBlock(sbImg.lendu(0), sbImg.lendu(40),
                              1024 ^ sbImg.lendu(24))

  val groupId = ((inodeIndex - 1) /* One-indexed */
                 / superblock.inodesPerGroup)
  val inodeIndexInGroup = (inodeIndex - 1) % superblock.inodesPerGroup
  val groupBlockArray:BA = if (1024 < superblock.blockSize) 1 else 2
  val groupBlockArrayOffset = superblock.toOffset(groupBlockArray)
  val descriptorOffset = 32 * groupId
  val gdImg = img.copy(shift=(groupBlockArrayOffset + descriptorOffset))
  val inodeTable:BA = gdImg.lendu(8)

  if (superblock.inodesCount <= inodeIndex) {
    throw new Exception("Invalid inode index")
  } else {
    val inodeIndexInTable = (inodeIndex - 1) % superblock.inodesPerGroup
    val inodePos = superblock.toOffset(inodeTable) + (inodeIndexInTable * 128)
    val inImg = img.copy(shift=inodePos)

    val fileSize = inImg.lendu(4)  //  file size
    val wholeBlocks = fileSize / superblock.blockSize
    val remainder = fileSize % superblock.blockSize
    var remainingBlocks = if (remainder > 0) wholeBlocks + 1 else wholeBlocks


    val dirBAs = directBlocks(inImg).take(remainingBlocks)
    for (ba <- dirBAs) {
      if (remainingBlocks > 0) {
        val size = {
          if (remainingBlocks > 1 || remainder == 0) superblock.blockSize
          else remainder
        }
        writeTo.write(readDataBlock(file, ba, superblock, size), 0, size)
        remainingBlocks -= 1
      }
    }
    if (remainingBlocks > 0) {
      //first indirection
      val indirBAs = indirectBlocks(img, superblock,
                                    superblock.toOffset(inImg.lendu(88)))
      for (ba <- indirBAs) {
        if (remainingBlocks > 0) {
          val size = {
            if (remainingBlocks > 1 || remainder == 0) superblock.blockSize
            else remainder
          }
          writeTo.write(readDataBlock(file, ba, superblock, size), 0, size)
          remainingBlocks -= 1
        }
      }
    }
    if (remainingBlocks > 0) {
      //double indirection
      val indirBA2s = indirectBlocks(img, superblock,
                                     superblock.toOffset(inImg.lendu(92)))
      for (indirBA <- indirBA2s) {
        if (remainingBlocks > 0) {
          val indirBAs = indirectBlocks(img, superblock,
                                        superblock.toOffset(indirBA))
          for (ba <- indirBAs) {
            if (remainingBlocks > 0) {
              val size = {
                if (remainingBlocks > 1 || remainder == 0) superblock.blockSize
                else remainder
              }
              writeTo.write(readDataBlock(file, ba, superblock, size), 0, size)
              remainingBlocks -= 1
            }
          }
        }
      }
      
    }
    println("%d bytes extracted".format(fileSize))
  }
}

if (args.length < 3) {
  println("Not enough arguments")
  println("Usage:")
  println("\tscala extractExt2.scala drive.dd inode output.file")
  println("\t\tdrive.dd is a disk image representing an Ext2 file system")
  println("\t\tinode is the inode number associated with the file")
  println("\t\toutput.file is the filename to which contents will be written")
  System.exit(1)
}

val inputFile = new RandomAccessFile(args(0), "r")
val inodeIndex = args(1).toInt
val outputFile = new FileOutputStream(args(2))
writeData(inputFile, inodeIndex, outputFile)
inputFile.close()
outputFile.close()

