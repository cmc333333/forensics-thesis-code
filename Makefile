default:
	coqc Fetch
	coqc ByteData
	coqc Util
	coqc FileIds
	coqc File
	coqc Ext2
	coqc FileNames
	coqc FileData
	coqc FileTypes
	coqc Tar
	coqc Timeline
	coqc HoneynetDefinitions
	coqc example_images

clean:
	rm -f *.vo *.glob

