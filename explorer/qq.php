<?php
include 'i/head.php';
include 'i/pg.php';
include 'i/search.php';
?>
</center>

<?php

function item($label,$v) {
    echo ($label);
    echo ("<pre>");
    echo (var_export($v) . "</pre>");
}

$json = pgj("querymg " . $_GET["b"]);

if (! (isset ($json->response))) {
  echo "<h3>No response obtained!</h3>";
} else if ($json->response == 'known') {
  foreach ($json->dbdata as $v) {
    echo "<pre>";
    echo (var_export($v));
  }
} else if ($json->response == 'unknown') {
    echo "<h2>No information about " . $_GET["b"] . "</h2>";
} else if ($json->response == 'pfgaddress') {
    echo "<pre>";
    echo (var_export($json));
} else {
    echo "<h2>Unknown Response!</h2>" . $json->response;
}

?>
</body>
