<?php include 'i/pg.php'; ?>

<?php

echo "<span>\n";
echo pg("displaysubitemhtml " . $_GET["d"] . " " . $_GET["i"] . " " . $_GET["l"] . " " . $_GET["n"] . " 20");
echo "</span>\n";

?>

