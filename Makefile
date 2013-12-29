default:
	coqc Fetch
	coqc ByteData
	coqc Util
	coqc FileSystems
	coqc File
	coqc Ext2
	coqc FileNames
	coqc FileData
	coqc FileTypes
	coqc Tar
	coqc Timeline
	coqc Ext2Lemmas
	coqc HoneynetDefinitions
	coqc example_images

clean:
	rm -f *.vo *.glob

