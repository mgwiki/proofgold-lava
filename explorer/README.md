# Install Litecoin

# Install ProofGold

# Enable open port for connection info

In proofgold.conf add:

  ip=1.1.1.1...
  port=20808...


# Enable swapping for exchange info

In proofgold.conf add:
  swapping=1

# Put the PHP code in a directory served by apache

## edit i/pg.php

Change password / port to those of your node RPC info that you set in your proofgold.conf

## Change "home/anon" to the place you keep mgwiki

In order to lookup mgwiki links

## Adjust paths in 'cron.mk' to update mgwiki links daily

Add a crontab entry, for example run crontab -e and add the line:

59 05 * * * /home/anon/www/pgbce/cron.mk > /dev/null 2>&1

## Adjust /home/anon in q.php

(For lookup by name)
