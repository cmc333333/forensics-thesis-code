#!/bin/bash
echo "Checking subset"
scala byteCheck.scala ../example_images.v $1 honeynet_map
echo "Extracting inode 23"
scala extractExt2.scala $1 23 /tmp/23.tgz
echo "Unzipping"
gunzip /tmp/23.tgz
echo "Checking file subset"
scala byteCheck.scala ../example_images.v /tmp/23.tar gunzipped_23
