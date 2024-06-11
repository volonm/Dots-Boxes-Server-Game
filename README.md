# Dots & Boxes project <br />
By: Joris Faas & Volodymyr Lysenko 




***

## Info for building and testing the software with a code editor

When building the software, all you need is the src directory and possibly also the test directory if you also wish to perform the tests that we have or if you want to make your own tests.<br />


## Info for building and testing the software with the executable files
To do this you would need to use the three .jar files that are included in the package called client.jar, ai.jar and server.jar. In the next section we will explain how to set up the necessary things to use the jar files and what you would need to do when using the executable files.

## Installation of the right programs
To actually run the .jar files on your computer you would first need to install java. <br />
You needs a specific version of java that works with the java compiler used in the program, the best option for this is the OpenJDK 19. https://www.oracle.com/java/technologies/javase/jdk19-archive-downloads.html , if this version doesn't work you can also try an earlier version.<br />
After having installed this for the right operating system, you can try to run the .jar files. <br /> <br />
You would first need to start the server to be able to accept client or ai, this can be done by opening your file explorer, copying the path that is leading to the directory where you have your jar file, then opening command prompt or any other terminal and typing cd PATH. now you're in the right directory. <br />
<br />
Now that you are in the right directory you can start up the server by typing "java -jar server.jar", this sets up the server and will ask you for a valid port number.
<br />
After this you can do the same with the client or the AI "java -jar client.jar" or "java -jar ai.jar" in a different command prompt. Now you're ready to start the client.

## How to play the game
The .jar files might not be the best way to play the game, since it does not always support colors on some terminals, but here is an explanation for if you are playing, no matter if it is on the .jar on in IntelliJ.
<br />
After having started the server, you can start the client. When starting you will first be asked to what server address you wish to connect to, this will either be a normal address or localhost when you want to play on the server on your computer. After this it will ask you for a port number, this is needed to make a connection between the client and the server. After the connection has been established you will be prompted to put in a username, after this the server will say hi to you and also confirms if your username is available or not, if not you will be asked to choose a different one.<br />
<br />
Now you're finally logged into the server. Now there will appear a menu on your screen with all the actions you can perform, but in this case you want to start a game. To do this you need to use the queue command, here you will be asked if you want to play as an AI or as a human and if you want to play as AI it will also ask if you want a smart or a dumb AI. After this you will be entered into the queue and also into the game when there are enough people in the queue. <br />
<br />
To actually play now you have to specify the move, when playing as a human you just need to specify where you want to place the line (if this field is a valid move). If you play as an AI all you have is join a game and the AI does the move for you automatically. You can play as many games as you want, only one at a time, and you can always use the menu command to see what else you can do.
<br /><br />
Hope the explanation was clear. Have a fun time playing Dots & Boxes!
