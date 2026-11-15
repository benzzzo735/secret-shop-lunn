FROM python:3.12-slim
WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt
COPY bot.py .
COPY webapp ./webapp
# База и фото живут в /data — подключите к нему постоянный том (volume)
ENV DB_PATH=/data/shop.db PHOTOS_DIR=/data/photos PYTHONUNBUFFERED=1
EXPOSE 8080
CMD ["python", "bot.py"]
