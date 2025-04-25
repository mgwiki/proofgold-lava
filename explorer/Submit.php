<?php
include 'i/head.php';
include 'i/pg.php';
include 'i/search.php';
?>
<h1>Send Proofgold Transaction</h1>
<table><tr><td><table><tr><td>

<form method="POST" action="">
   <textarea name="user_text" rows="5" cols="100" placeholder="Enter transaction"></textarea><br><br>
   <input type="submit" name="submit" value="Submit">
</form>

<?php
if (isset($_POST['submit'])) {
  $text = $_POST['user_text'];
  $text = trim($text);
  if (!empty($text)) {
     if (ctype_xdigit($text)) {
         echo ("Trying to submit[" . $text . "]<br/>");
         echo (strtok(pg("sendtx " . $text),"\n"));
     } else {
         echo "<p style='color:red;'>Invalid characters in a transaction.</p>";
     }
  } else {
    echo "<p style='color:red;'>Please enter a transaction.</p>";
  }
}
?>

</td></tr></table></td></tr></table></body></html>
