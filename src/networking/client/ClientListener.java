package networking.client;

/**
 * Listener pattern for the client.
 */
public interface ClientListener {
    /**
     * Notifies the listener that a message has been received.
     *
     * @param message the message received
     */
     void message(String message);

    /**
     * Notifies the listener that the connection to the server has been lost.
     */
     void connectionLost();
}
