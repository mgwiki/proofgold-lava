#!/bin/bash
cd /home/anon/mgw_test/etc
git pull
/home/anon/proofgold-lava-explorer/client/bin/proofgoldcli "converth2ta /home/anon/mgw_test/etc/rindex.txt /home/anon/mgw_test/etc/rindex2.txt"
. rproc
