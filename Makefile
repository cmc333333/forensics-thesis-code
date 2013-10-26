default:
	coqc ByteData
	coqc Util
	coqc File
	coqc Ext2
	coqc FileNames
	coqc FileTypes
	coqc FileSystems
	coqc Tar
	coqc Timeline
	coqc example_images

clean:
	rm -f *.vo *.glob

