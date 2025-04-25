<?php
include 'i/head.php';
include 'i/pg.php';
include 'i/search.php';
//exec("dot -Tsvg /home/cezary/proofgold-lava/client/graph.dot -o /var/www/html/formalweb3/pgbce/graph.svg > /dev/null 2>&1"
$filename = '/home/cezary/proofgold-lava/client/graph.dot';
if (file_exists($filename)) {
    $fileAge = time() - filemtime($filename);
    if ($fileAge > 60) { // 60 seconds = 1 minute
        // Your command here
        echo "File is older than 1 minute, regenerating";
        pg("chaingraph");
    } else {
        echo "File is not older than 1 minute.";
    }
} else {
    echo "File does not exist.";
}
?>
<h1>Proofgold status</h1>
<!--<object data="path/to/your/image.svg" type="image/svg+xml" style="width: 100%; height: auto;"></object>-->
<?php
readfile('graph.svg');
?>
</body></html>

